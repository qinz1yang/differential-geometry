/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualPatch

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3}

theorem section34Incident_iff_mem_of_subset_segment {e s : Finset E3} (hs : s ∈ K.faces)
    {u v : E3} (huv : ({u, v} : Finset E3) ∈ K.faces) (he2 : 1 < e.card)
    (he : convexHull ℝ (e : Set E3) ⊆ segment ℝ u v) (hus : u ∈ s) :
    Section34Incident e s ↔ v ∈ s := by
  refine ⟨fun h => ?_, fun hvs => section34Incident_of_subset_segment he hus hvs⟩
  by_contra hvs
  obtain ⟨x, hx, hxu⟩ := Finset.exists_mem_ne he2 u
  exact not_section34Incident_of_notMem_right hs huv hx (he (subset_convexHull ℝ _ hx)) hxu hvs h

theorem Section34CompactCutFrame.exists_patchEnum_of_vertex
    (hcut : Section34CompactCutFrame C K K' src srcBd) {t : Section34CompactSimplexIndex K 4}
    {a b c d : E3} (htabcd : t.1 = {a, b, c, d}) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {w : Section34CompactVertexIndex K K'}
    (hwa : w.1 = {a}) :
    ∃ (sK : Fin 3 → Section34CompactSimplexIndex K 3)
      (eK : Fin 3 → Section34CompactEdgeIndex K K'),
      (∀ k, Section34Incident (sK k).1 t.1) ∧ (∀ k, Section34Incident w.1 (sK k).1) ∧
      (∀ k, w.1 ⊆ (eK k).1) ∧ Function.Injective sK ∧ Function.Injective eK ∧
      (∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k) ∧
      (∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
        Section34Incident w.1 s.1 → ∃ k, s = sK k) ∧
      ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 t.1 → w.1 ⊆ e.1 →
        ∃ k, e = eK k := by
  classical
  obtain ⟨-, -, -, -, hsub, -⟩ := id hcut
  have ht := t.2.1
  have hmem : ∀ x, x ∈ ({a, b, c, d} : Finset E3) → x ∈ t.1 := fun x hx => by
    rw [htabcd]
    exact hx
  have ha : a ∈ t.1 := hmem a (by simp)
  have hb : b ∈ t.1 := hmem b (by simp)
  have hc : c ∈ t.1 := hmem c (by simp)
  have hd : d ∈ t.1 := hmem d (by simp)
  have hpair : ∀ {x y : E3}, x ∈ t.1 → y ∈ t.1 → ({x, y} : Finset E3) ∈ K.faces :=
    fun hx hy => K.down_closed ht (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
      (Finset.insert_nonempty _ _)
  have hvert : ({a} : Finset E3) ∈ K.faces :=
    K.down_closed ht (Finset.singleton_subset_iff.mpr ha) (Finset.singleton_nonempty a)
  have hface : ∀ {x y z : E3}, x ∈ t.1 → y ∈ t.1 → z ∈ t.1 → x ≠ y → x ≠ z → y ≠ z →
      ({x, y, z} : Finset E3) ∈ K.faces ∧ ({x, y, z} : Finset E3).card = 3 :=
    fun hx hy hz hxy hxz hyz =>
      ⟨K.down_closed ht (Finset.insert_subset hx (Finset.insert_subset hy
        (Finset.singleton_subset_iff.mpr hz))) (Finset.insert_nonempty _ _),
        Finset.card_eq_three.mpr ⟨_, _, _, hxy, hxz, hyz, rfl⟩⟩
  have hsub3 : ∀ {x y z : E3}, x ∈ t.1 → y ∈ t.1 → z ∈ t.1 →
      Section34Incident ({x, y, z} : Finset E3) t.1 := fun hx hy hz q hq =>
    subset_convexHull ℝ _ ((Finset.insert_subset hx (Finset.insert_subset hy
      (Finset.singleton_subset_iff.mpr hz))) hq)
  have hwinc : ∀ s : Finset E3, a ∈ s → Section34Incident w.1 s := fun s has q hq => by
    rw [hwa, Finset.coe_singleton, mem_singleton_iff] at hq
    rw [hq]
    exact subset_convexHull ℝ _ has
  obtain ⟨eb, haeb, hebseg, hebu⟩ := hcut.exists_edgeIndex_mem_subset_segment hab (hpair ha hb)
  obtain ⟨ec, haec, hecseg, hecu⟩ := hcut.exists_edgeIndex_mem_subset_segment hac (hpair ha hc)
  obtain ⟨ed, haed, hedseg, hedu⟩ := hcut.exists_edgeIndex_mem_subset_segment had (hpair ha hd)
  have hcard2 : ∀ e : Section34CompactEdgeIndex K K', 1 < e.1.card := fun e => by
    rw [e.2.2.1]
    norm_num
  have hedge_ne : ∀ {e e' : Section34CompactEdgeIndex K K'} {x y : E3}, x ∈ t.1 → y ∈ t.1 →
      x ≠ y → convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ a x →
      convexHull ℝ (e'.1 : Set E3) ⊆ segment ℝ a y → e ≠ e' := by
    intro e e' x y hx hy hxy he he' hee
    obtain ⟨z, hz, hza⟩ := Finset.exists_mem_ne (hcard2 e) a
    have hz1 := he (subset_convexHull ℝ _ hz)
    have hz2 : z ∈ segment ℝ a y := he' (by rw [← hee]; exact subset_convexHull ℝ _ hz)
    exact hza (segment_inter_segment_subset_singleton_of_mem_faces ht ha hx hy hxy ⟨hz1, hz2⟩)
  let sabd : Section34CompactSimplexIndex K 3 := ⟨{a, b, d}, hface ha hb hd hab had hbd⟩
  let sabc : Section34CompactSimplexIndex K 3 := ⟨{a, b, c}, hface ha hb hc hab hac hbc⟩
  let sacd : Section34CompactSimplexIndex K 3 := ⟨{a, c, d}, hface ha hc hd hac had hcd⟩
  have hsne : ∀ {s s' : Section34CompactSimplexIndex K 3} {x : E3}, x ∈ s'.1 → x ∉ s.1 →
      s ≠ s' := fun hx hxs h => hxs (by rw [h]; exact hx)
  have h01 : sabd ≠ sabc := hsne (x := c) (by simp [sabc]) (by
    simp only [sabd, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hac.symm, hbc.symm, hcd⟩)
  have h02 : sabd ≠ sacd := hsne (x := c) (by simp [sacd]) (by
    simp only [sabd, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hac.symm, hbc.symm, hcd⟩)
  have h12 : sabc ≠ sacd := hsne (x := d) (by simp [sacd]) (by
    simp only [sabc, Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨had.symm, hbd.symm, hcd.symm⟩)
  have hbc' := hedge_ne hb hc hbc hebseg hecseg
  have hbd' := hedge_ne hb hd hbd hebseg hedseg
  have hcd' := hedge_ne hc hd hcd hecseg hedseg
  have hib : ∀ s : Finset E3, s ∈ K.faces → a ∈ s → (Section34Incident eb.1 s ↔ b ∈ s) :=
    fun s hs has => section34Incident_iff_mem_of_subset_segment hs (hpair ha hb) (hcard2 eb)
      hebseg has
  have hic : ∀ s : Finset E3, s ∈ K.faces → a ∈ s → (Section34Incident ec.1 s ↔ c ∈ s) :=
    fun s hs has => section34Incident_iff_mem_of_subset_segment hs (hpair ha hc) (hcard2 ec)
      hecseg has
  have hid : ∀ s : Finset E3, s ∈ K.faces → a ∈ s → (Section34Incident ed.1 s ↔ d ∈ s) :=
    fun s hs has => section34Incident_iff_mem_of_subset_segment hs (hpair ha hd) (hcard2 ed)
      hedseg has
  have i00 : Section34Incident eb.1 sabd.1 := (hib _ sabd.2.1 (by simp [sabd])).mpr (by simp [sabd])
  have i01 : ¬ Section34Incident ec.1 sabd.1 := fun h => by
    have h' := (hic _ sabd.2.1 (by simp [sabd])).mp h
    simp only [sabd, Finset.mem_insert, Finset.mem_singleton] at h'
    rcases h' with h' | h' | h'
    · exact hac h'.symm
    · exact hbc h'.symm
    · exact hcd h'
  have i02 : Section34Incident ed.1 sabd.1 := (hid _ sabd.2.1 (by simp [sabd])).mpr (by simp [sabd])
  have i10 : Section34Incident eb.1 sabc.1 := (hib _ sabc.2.1 (by simp [sabc])).mpr (by simp [sabc])
  have i11 : Section34Incident ec.1 sabc.1 := (hic _ sabc.2.1 (by simp [sabc])).mpr (by simp [sabc])
  have i12 : ¬ Section34Incident ed.1 sabc.1 := fun h => by
    have h' := (hid _ sabc.2.1 (by simp [sabc])).mp h
    simp only [sabc, Finset.mem_insert, Finset.mem_singleton] at h'
    rcases h' with h' | h' | h'
    · exact had h'.symm
    · exact hbd h'.symm
    · exact hcd h'.symm
  have i20 : ¬ Section34Incident eb.1 sacd.1 := fun h => by
    have h' := (hib _ sacd.2.1 (by simp [sacd])).mp h
    simp only [sacd, Finset.mem_insert, Finset.mem_singleton] at h'
    rcases h' with h' | h' | h'
    · exact hab h'.symm
    · exact hbc h'
    · exact hbd h'
  have i21 : Section34Incident ec.1 sacd.1 := (hic _ sacd.2.1 (by simp [sacd])).mpr (by simp [sacd])
  have i22 : Section34Incident ed.1 sacd.1 := (hid _ sacd.2.1 (by simp [sacd])).mpr (by simp [sacd])
  refine ⟨![sabd, sabc, sacd], ![eb, ec, ed], fun k => ?_, fun k => ?_, fun k => ?_,
    fun i j hij => ?_, fun i j hij => ?_, fun k l => ?_, fun s hs hws => ?_,
    fun e he hwe => ?_⟩
  · fin_cases k
    · exact hsub3 ha hb hd
    · exact hsub3 ha hb hc
    · exact hsub3 ha hc hd
  · fin_cases k
    · exact hwinc _ (by simp [sabd])
    · exact hwinc _ (by simp [sabc])
    · exact hwinc _ (by simp [sacd])
  · rw [hwa]
    fin_cases k
    · exact Finset.singleton_subset_iff.mpr haeb
    · exact Finset.singleton_subset_iff.mpr haec
    · exact Finset.singleton_subset_iff.mpr haed
  · fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact absurd hij h01
      | exact absurd hij h01.symm
      | exact absurd hij h02
      | exact absurd hij h02.symm
      | exact absurd hij h12
      | exact absurd hij h12.symm
  · fin_cases i <;> fin_cases j
    all_goals first
      | rfl
      | exact absurd hij hbc'
      | exact absurd hij hbc'.symm
      | exact absurd hij hbd'
      | exact absurd hij hbd'.symm
      | exact absurd hij hcd'
      | exact absurd hij hcd'.symm
  · fin_cases k <;> fin_cases l
    · exact iff_of_true i00 (by decide)
    · exact iff_of_false i01 (by decide)
    · exact iff_of_true i02 (by decide)
    · exact iff_of_true i10 (by decide)
    · exact iff_of_true i11 (by decide)
    · exact iff_of_false i12 (by decide)
    · exact iff_of_false i20 (by decide)
    · exact iff_of_true i21 (by decide)
    · exact iff_of_true i22 (by decide)
  · rcases section34CompactSimplexIndex_eq_of_incident ht htabcd hab hac had hbc hbd hcd s hs with
      h | h | h | h
    · exact ⟨2, Subtype.ext h⟩
    · exact ⟨1, Subtype.ext h⟩
    · refine absurd hws (not_section34Incident_of_notMem_left s.2.1 hvert
        (by rw [hwa]; exact Finset.mem_singleton_self a) ?_)
      rw [h]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, hac, had⟩
    · exact ⟨0, Subtype.ext h⟩
  · have hae : a ∈ e.1 := hwe (by rw [hwa]; exact Finset.mem_singleton_self a)
    obtain ⟨x, hx, y, hy, hxy, hexy⟩ :=
      exists_segment_of_incident_section34CompactEdgeIndex hsub ht e he
    have hax : a ∈ segment ℝ x y := hexy (subset_convexHull ℝ _ hae)
    have ha' := mem_convexHull_inter_of_mem_segment hvert (hpair hx hy) hax
      (by rw [Finset.coe_singleton, convexHull_singleton]; exact mem_singleton a)
    have hay : a = x ∨ a = y := by
      by_contra hne
      rw [not_or] at hne
      have hnot : a ∉ ({x, y} : Finset E3) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact hne
      rw [Finset.inter_singleton_of_notMem hnot, Finset.coe_empty, convexHull_empty] at ha'
      exact ha'
    obtain ⟨z, hz, hza, hez⟩ : ∃ z ∈ t.1, z ≠ a ∧
        convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ a z := by
      rcases hay with h | h
      · rw [← h] at hexy
        exact ⟨y, hy, by rw [← h] at hxy; exact hxy.symm, hexy⟩
      · rw [← h, segment_symm] at hexy
        exact ⟨x, hx, by rw [← h] at hxy; exact hxy, hexy⟩
    rw [htabcd] at hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hz | hz | hz | hz
    · exact absurd hz hza
    · rw [hz] at hez
      exact ⟨0, hebu e hae hez⟩
    · rw [hz] at hez
      exact ⟨1, hecu e hae hez⟩
    · rw [hz] at hez
      exact ⟨2, hedu e hae hez⟩

theorem eq_or_eq_of_mem_convexHull_inter_pair {x y a b p : E3}
    (hp : p ∈ convexHull ℝ (({x, y} : Set E3) ∩ {a, b})) (hpb : p ≠ b) : a = x ∨ a = y := by
  by_contra hne
  rw [not_or] at hne
  have hsub : ({x, y} : Set E3) ∩ {a, b} ⊆ {b} := by
    rintro z ⟨hz1, hz2⟩
    rcases hz2 with hz2 | hz2
    · exfalso
      rw [hz2] at hz1
      rcases hz1 with h | h
      · exact hne.1 h
      · exact hne.2 h
    · exact hz2
  have h := convexHull_mono hsub hp
  rw [convexHull_singleton] at h
  exact hpb h

theorem Section34CompactCutFrame.exists_patchEnum_of_edge
    (hcut : Section34CompactCutFrame C K K' src srcBd) {t : Section34CompactSimplexIndex K 4}
    {a b c d : E3} (htabcd : t.1 = {a, b, c, d}) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {w : Section34CompactVertexIndex K K'} {p : E3}
    (hwp : w.1 = {p}) (hp : p ∈ segment ℝ a b) (hpa : p ≠ a) (hpb : p ≠ b) :
    ∃ (sK : Fin 2 → Section34CompactSimplexIndex K 3)
      (eK : Fin 2 → Section34CompactEdgeIndex K K'),
      (∀ k, Section34Incident (sK k).1 t.1) ∧ (∀ k, Section34Incident w.1 (sK k).1) ∧
      (∀ k, w.1 ⊆ (eK k).1) ∧ Function.Injective sK ∧ Function.Injective eK ∧
      (∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k) ∧
      (∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
        Section34Incident w.1 s.1 → ∃ k, s = sK k) ∧
      ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 t.1 → w.1 ⊆ e.1 →
        ∃ k, e = eK k := by
  classical
  obtain ⟨-, -, -, -, hsub, -⟩ := id hcut
  have ht := t.2.1
  have hmem : ∀ x, x ∈ ({a, b, c, d} : Finset E3) → x ∈ t.1 := fun x hx => by
    rw [htabcd]
    exact hx
  have ha : a ∈ t.1 := hmem a (by simp)
  have hb : b ∈ t.1 := hmem b (by simp)
  have hc : c ∈ t.1 := hmem c (by simp)
  have hd : d ∈ t.1 := hmem d (by simp)
  have hpair : ∀ {x y : E3}, x ∈ t.1 → y ∈ t.1 → ({x, y} : Finset E3) ∈ K.faces :=
    fun hx hy => K.down_closed ht (Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy))
      (Finset.insert_nonempty _ _)
  have hface : ∀ {x y z : E3}, x ∈ t.1 → y ∈ t.1 → z ∈ t.1 → x ≠ y → x ≠ z → y ≠ z →
      ({x, y, z} : Finset E3) ∈ K.faces ∧ ({x, y, z} : Finset E3).card = 3 :=
    fun hx hy hz hxy hxz hyz =>
      ⟨K.down_closed ht (Finset.insert_subset hx (Finset.insert_subset hy
        (Finset.singleton_subset_iff.mpr hz))) (Finset.insert_nonempty _ _),
        Finset.card_eq_three.mpr ⟨_, _, _, hxy, hxz, hyz, rfl⟩⟩
  have hsub3 : ∀ {x y z : E3}, x ∈ t.1 → y ∈ t.1 → z ∈ t.1 →
      Section34Incident ({x, y, z} : Finset E3) t.1 := fun hx hy hz q hq =>
    subset_convexHull ℝ _ ((Finset.insert_subset hx (Finset.insert_subset hy
      (Finset.singleton_subset_iff.mpr hz))) hq)
  have hpw : p ∈ w.1 := by
    rw [hwp]
    exact Finset.mem_singleton_self p
  have hwinc : ∀ s : Finset E3, a ∈ s → b ∈ s → Section34Incident w.1 s := fun s has hbs q hq => by
    rw [hwp, Finset.coe_singleton, mem_singleton_iff] at hq
    rw [hq]
    exact (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ has)
      (subset_convexHull ℝ _ hbs) hp
  have hcard2 : ∀ e : Section34CompactEdgeIndex K K', 1 < e.1.card := fun e => by
    rw [e.2.2.1]
    norm_num
  have hedge_eq : ∀ e e' : Section34CompactEdgeIndex K K', e.1 ⊆ e'.1 → e = e' := fun e e' h =>
    Subtype.ext (Finset.eq_of_subset_of_card_le h (by rw [e.2.2.1, e'.2.2.1]))
  obtain ⟨n, wv, ev, -, hw0, hwn, hwpt, hev, -, hsurj, hfar⟩ :=
    hcut.exists_vertexIndex_path hab (hpair ha hb)
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
  let sabc : Section34CompactSimplexIndex K 3 := ⟨{a, b, c}, hface ha hb hc hab hac hbc⟩
  let sabd : Section34CompactSimplexIndex K 3 := ⟨{a, b, d}, hface ha hb hd hab had hbd⟩
  have hne_s : sabc ≠ sabd := fun h => by
    have hc' : c ∈ ({a, b, d} : Finset E3) := by
      have h' : ({a, b, c} : Finset E3) = {a, b, d} := congrArg Subtype.val h
      rw [← h']
      simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
    rcases hc' with h' | h' | h'
    · exact hac h'.symm
    · exact hbc h'.symm
    · exact hcd h'
  have hinc_all : ∀ i < n, ∀ s : Finset E3, a ∈ s → b ∈ s → Section34Incident (ev i).1 s :=
    fun i hi s has hbs => section34Incident_of_subset_segment (hevseg i hi) has hbs
  refine ⟨![sabc, sabd], ![ev j, ev (j + 1)], fun k => ?_, fun k => ?_, fun k => ?_,
    fun i' j' hij => ?_, fun i' j' hij => ?_, fun k l => ?_, fun s hs hws => ?_,
    fun e he hwe => ?_⟩
  · fin_cases k
    · exact hsub3 ha hb hc
    · exact hsub3 ha hb hd
  · fin_cases k
    · exact hwinc _ (by simp [sabc]) (by simp [sabc])
    · exact hwinc _ (by simp [sabd]) (by simp [sabd])
  · fin_cases k
    · exact hwe0
    · exact hwe1
  · fin_cases i' <;> fin_cases j'
    all_goals first
      | rfl
      | exact absurd hij hne_s
      | exact absurd hij hne_s.symm
  · fin_cases i' <;> fin_cases j'
    all_goals first
      | rfl
      | exact absurd hij hne_e
      | exact absurd hij hne_e.symm
  · fin_cases k <;> fin_cases l
    · exact iff_of_true (hinc_all j (by omega) _ (by simp [sabc]) (by simp [sabc])) (by decide)
    · exact iff_of_true (hinc_all (j + 1) (by omega) _ (by simp [sabc]) (by simp [sabc]))
        (by decide)
    · exact iff_of_true (hinc_all j (by omega) _ (by simp [sabd]) (by simp [sabd])) (by decide)
    · exact iff_of_true (hinc_all (j + 1) (by omega) _ (by simp [sabd]) (by simp [sabd]))
        (by decide)
  · rcases section34CompactSimplexIndex_eq_of_incident ht htabcd hab hac had hbc hbd hcd s hs with
      h | h | h | h
    · refine absurd hws (not_section34Incident_of_notMem_right s.2.1 (hpair ha hb) hpw hp hpa ?_)
      rw [h]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab.symm, hbc, hbd⟩
    · exact ⟨0, Subtype.ext h⟩
    · refine absurd hws (not_section34Incident_of_notMem_right s.2.1 (hpair hb ha) hpw
        (by rw [segment_symm]; exact hp) hpb ?_)
      rw [h]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, hac, had⟩
    · exact ⟨1, Subtype.ext h⟩
  · have hpe : p ∈ e.1 := hwe hpw
    obtain ⟨x, hx, y, hy, hxy, hexy⟩ :=
      exists_segment_of_incident_section34CompactEdgeIndex hsub ht e he
    have hpxy : p ∈ segment ℝ x y := hexy (subset_convexHull ℝ _ hpe)
    have hpc := segment_inter_segment_subset_of_mem_faces (hpair hx hy) (hpair ha hb) ⟨hpxy, hp⟩
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
    · refine ⟨0, (hedge_eq (ev j) e ?_).symm⟩
      rw [hev j (by omega)]
      rw [h] at hqe
      exact Finset.union_subset hqe hpe'
    · refine ⟨1, (hedge_eq (ev (j + 1)) e ?_).symm⟩
      rw [hev (j + 1) (by omega)]
      rw [h] at hqe
      exact Finset.union_subset hpe' hqe

theorem Section34CompactCutFrame.exists_patchEnum
    (hcut : Section34CompactCutFrame C K K' src srcBd) (t : Section34CompactSimplexIndex K 4)
    {w : Section34CompactVertexIndex K K'} (hw : Section34Incident w.1 t.1) :
    ∃ (m : ℕ) (sK : Fin (m + 2) → Section34CompactSimplexIndex K 3)
      (eK : Fin (m + 2) → Section34CompactEdgeIndex K K'),
      (∀ k, Section34Incident (sK k).1 t.1) ∧ (∀ k, Section34Incident w.1 (sK k).1) ∧
      (∀ k, w.1 ⊆ (eK k).1) ∧ Function.Injective sK ∧ Function.Injective eK ∧
      (∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k) ∧
      (∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
        Section34Incident w.1 s.1 → ∃ k, s = sK k) ∧
      ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 t.1 → w.1 ⊆ e.1 →
        ∃ k, e = eK k := by
  classical
  obtain ⟨p, hwp⟩ := Finset.card_eq_one.mp w.2.2.1
  have hpw : p ∈ (w.1 : Set E3) := by
    rw [hwp]
    exact Finset.mem_coe.mpr (Finset.mem_singleton_self p)
  obtain ⟨x, hx, y, hy, hpxy⟩ := exists_mem_segment_of_mem_convexHull_graphSkeleton t.2.1
    (hw hpw) (w.2.2.2 (subset_convexHull ℝ _ hpw))
  have hvertex : ∀ v ∈ t.1, p = v → ∃ (sK : Fin 3 → Section34CompactSimplexIndex K 3)
      (eK : Fin 3 → Section34CompactEdgeIndex K K'),
      (∀ k, Section34Incident (sK k).1 t.1) ∧ (∀ k, Section34Incident w.1 (sK k).1) ∧
      (∀ k, w.1 ⊆ (eK k).1) ∧ Function.Injective sK ∧ Function.Injective eK ∧
      (∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k) ∧
      (∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
        Section34Incident w.1 s.1 → ∃ k, s = sK k) ∧
      ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 t.1 → w.1 ⊆ e.1 →
        ∃ k, e = eK k := by
    intro v hv hpv
    have hcard : (t.1.erase v).card = 3 := by
      rw [Finset.card_erase_of_mem hv, t.2.2]
    obtain ⟨b, c, d, hbc, hbd, hcd, hbcd⟩ := Finset.card_eq_three.mp hcard
    have hmem : ∀ z, z ∈ ({b, c, d} : Finset E3) → z ≠ v := fun z hz => by
      rw [← hbcd] at hz
      exact Finset.ne_of_mem_erase hz
    have htv : t.1 = {v, b, c, d} := by
      rw [← Finset.insert_erase hv, hbcd]
    exact hcut.exists_patchEnum_of_vertex htv (hmem b (by simp)).symm (hmem c (by simp)).symm
      (hmem d (by simp)).symm hbc hbd hcd (by rw [hwp, hpv])
  by_cases hpx : p = x
  · obtain ⟨sK, eK, h⟩ := hvertex x hx hpx
    exact ⟨1, sK, eK, h⟩
  by_cases hpy : p = y
  · obtain ⟨sK, eK, h⟩ := hvertex y hy hpy
    exact ⟨1, sK, eK, h⟩
  have hxy : x ≠ y := by
    intro h
    rw [h, segment_same, mem_singleton_iff] at hpxy
    exact hpy hpxy
  have hy' : y ∈ t.1.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hy⟩
  have hcard : ((t.1.erase x).erase y).card = 2 := by
    rw [Finset.card_erase_of_mem hy', Finset.card_erase_of_mem hx, t.2.2]
  obtain ⟨c, d, hcd, hcdeq⟩ := Finset.card_eq_two.mp hcard
  have hmem : ∀ z, z ∈ ({c, d} : Finset E3) → z ≠ y ∧ z ≠ x := fun z hz => by
    rw [← hcdeq] at hz
    exact ⟨Finset.ne_of_mem_erase hz, Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hz)⟩
  have htxy : t.1 = {x, y, c, d} := by
    rw [← Finset.insert_erase hx, ← Finset.insert_erase hy', hcdeq]
  obtain ⟨sK, eK, h⟩ := hcut.exists_patchEnum_of_edge htxy hxy (hmem c (by simp)).2.symm
    (hmem d (by simp)).2.symm (hmem c (by simp)).1.symm (hmem d (by simp)).1.symm hcd hwp hpxy
    hpx hpy
  exact ⟨0, sK, eK, h⟩

end DifferentialGeometry.Topology.PiecewiseLinear
