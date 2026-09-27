/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellChartGluing
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ClawIncidence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {f₁ : M₁ → M₂}

theorem Section34CutFrame.isPLCellOn_section34ClawBall
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hf₁ : IsPLHomeomorphInto 3 f₁ (section34CutNeighborhood src))
    {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) {x y x' y' : Ea} (hx : x ∈ t) (hy : y ∈ t)
    (hx' : x' ∈ t) (hy' : y' ∈ t) (hxy : x ≠ y) (hxx' : x ≠ x') (hyy' : y ≠ y')
    (hxy' : x ≠ y') (hyx' : y ≠ x') (hx'y' : x' ≠ y')
    {c : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M₂)
    (hVc : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 t →
      section34VertexBallImage src f₁ w ⊆ c.source) :
    IsPLCellOn 3 (section34ClawBall (section34VertexBallImage src f₁) x y x' y')
      (frontier (section34ClawBall (section34VertexBallImage src f₁) x y x' y')) := by
  classical
  have hface : ∀ {a b : Ea}, a ∈ t → b ∈ t → ({a, b} : Finset Ea) ∈ 𝒦.complex.faces := fun ha hb =>
    𝒦.complex.down_closed ht (Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb))
      (Finset.insert_nonempty _ _)
  have hVball : ∀ w, IsPLCellOn 3 (section34VertexBallImage src f₁ w)
      (section34VertexBallImage srcBd f₁ w) := hcut.isPLCellOn_vertexBallImage hf₁
  have hEball : ∀ e, IsPLCellOn 2 (section34SplitDiskImage src f₁ e)
      (section34SplitDiskImage srcBd f₁ e) := hcut.isPLCellOn_splitDiskImage hf₁
  have hsegt : ∀ {a b : Ea}, a ∈ t → b ∈ t → segment ℝ a b ⊆ convexHull ℝ (t : Set Ea) :=
    fun ha hb => (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ ha)
      (subset_convexHull ℝ _ hb)
  have hsing : ∀ {w : Section34VertexIndex 𝒦 𝒦'} {p : Ea}
      (e' : Section34EdgeIndex 𝒦 𝒦'), w.1 = {p} → w.1 ⊆ e'.1 → p ∈ e'.1 :=
    fun _ hw hwe => hwe (by rw [hw]; exact Finset.mem_singleton_self _)
  have hinc : ∀ (e' : Section34EdgeIndex 𝒦 𝒦') (p q : Ea), p ≠ q → p ∈ e'.1 →
      q ∈ e'.1 → p ∈ convexHull ℝ (t : Set Ea) → q ∈ convexHull ℝ (t : Set Ea) →
      Section34Incident e'.1 t := by
    intro e' p q hpq hp hq hpt hqt z hz
    have hpair : ({p, q} : Finset Ea) = e'.1 := Finset.eq_of_subset_of_card_le
      (Finset.insert_subset hp (Finset.singleton_subset_iff.mpr hq))
      (by rw [e'.2.2.1, Finset.card_pair hpq])
    rw [← hpair] at hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hpt
    · rw [Finset.mem_singleton.mp hz]
      exact hqt
  have hmeet2 : ∀ {a b c : Ea}, a ∈ t → b ∈ t → c ∈ t → b ≠ c →
      segment ℝ a b ∩ segment ℝ a c ⊆ {a} := by
    intro a b c ha hb hc hbc z hz
    have h := SimplicialComplex.segment_inter_segment_subset (hface ha hb) (hface ha hc) hz
    have hset : ({a, b} : Set Ea) ∩ {a, c} ⊆ {a} := by
      rintro u ⟨hu1, hu2⟩
      rcases hu1 with hu1 | hu1
      · rw [hu1]
        exact mem_singleton _
      · rw [mem_singleton_iff.mp hu1] at hu2 ⊢
        rcases hu2 with h' | h'
        · rw [h']
          exact mem_singleton _
        · exact absurd (mem_singleton_iff.mp h') hbc
    have h' := convexHull_mono hset h
    rwa [convexHull_singleton] at h'
  have hmeet0 : ∀ {a b c d : Ea}, a ∈ t → b ∈ t → c ∈ t → d ∈ t → a ≠ c → a ≠ d →
      b ≠ c → b ≠ d → Disjoint (segment ℝ a b) (segment ℝ c d) := by
    intro a b c d ha hb hc hd hac had hbc hbd
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    have h := SimplicialComplex.segment_inter_segment_subset (hface ha hb) (hface hc hd) ⟨hz, hz'⟩
    have hset : ({a, b} : Set Ea) ∩ {c, d} = ∅ := by
      refine eq_empty_of_forall_notMem fun u hu => ?_
      rcases hu.1 with hu1 | hu1 <;> rcases hu.2 with hu2 | hu2
      · exact hac (hu1.symm.trans hu2)
      · exact had (hu1.symm.trans (mem_singleton_iff.mp hu2))
      · exact hbc ((mem_singleton_iff.mp hu1).symm.trans hu2)
      · exact hbd ((mem_singleton_iff.mp hu1).symm.trans (mem_singleton_iff.mp hu2))
    rw [hset, convexHull_empty] at h
    exact h
  have hmemU : ∀ (B : Set M₂) (W : ℕ → Set M₂) (k : ℕ) (z : M₂),
      z ∈ B ∪ ⋃ j ∈ Finset.range k, W (j + 1) ↔ z ∈ B ∨ ∃ j, 0 < j ∧ j ≤ k ∧ z ∈ W j := by
    intro B W k z
    simp only [mem_union, mem_iUnion, Finset.mem_range, exists_prop]
    constructor
    · rintro (h | ⟨j, hj, hz⟩)
      · exact Or.inl h
      · exact Or.inr ⟨j + 1, by omega, by omega, hz⟩
    · rintro (h | ⟨j, hj0, hjk, hz⟩)
      · exact Or.inl h
      · refine Or.inr ⟨j - 1, by omega, ?_⟩
        rw [Nat.sub_add_cancel hj0]
        exact hz
  obtain ⟨n₀, w₀, e₀, -, hw₀0, hw₀n, hw₀pt, he₀, hw₀inj, hw₀surj, hw₀far⟩ :=
    hcut.exists_vertexIndex_path hxy (hface hx hy)
  obtain ⟨n₁, w₁, e₁, -, hw₁0, hw₁n, hw₁pt, he₁, hw₁inj, hw₁surj, hw₁far⟩ :=
    hcut.exists_vertexIndex_path hxx' (hface hx hx')
  obtain ⟨n₂, w₂, e₂, -, hw₂0, hw₂n, hw₂pt, he₂, hw₂inj, hw₂surj, hw₂far⟩ :=
    hcut.exists_vertexIndex_path hyy' (hface hy hy')
  set V := section34VertexBallImage src f₁
  have hVseg : ∀ {a b : Ea}, a ∈ t → b ∈ t →
      ∀ {w : Section34VertexIndex 𝒦 𝒦'} {p : Ea}, w.1 = {p} →
        p ∈ segment ℝ a b → V w ⊆ c.source := by
    intro a b ha hb w p hwp hp
    apply hVc w
    rw [Section34Incident, hwp, Finset.coe_singleton, singleton_subset_iff]
    exact hsegt ha hb hp
  have hW₀c : ∀ i ≤ n₀, V (w₀ i) ⊆ c.source := by
    intro i hi
    obtain ⟨p, hp, hwp, -⟩ := hw₀pt i hi
    exact hVseg hx hy hwp hp
  have hW₁c : ∀ i ≤ n₁, V (w₁ i) ⊆ c.source := by
    intro i hi
    obtain ⟨p, hp, hwp, -⟩ := hw₁pt i hi
    exact hVseg hx hx' hwp hp
  have hW₂c : ∀ i ≤ n₂, V (w₂ i) ⊆ c.source := by
    intro i hi
    obtain ⟨p, hp, hwp, -⟩ := hw₂pt i hi
    exact hVseg hy hy' hwp hp
  have hfront : ∀ {e : Section34EdgeIndex 𝒦 𝒦'} {w w' : Section34VertexIndex 𝒦 𝒦'},
      e.1 = w.1 ∪ w'.1 → section34SplitDiskImage src f₁ e ⊆ frontier (V w') :=
    fun h => hcut.splitDiskImage_subset_frontier hf₁ (by rw [h]; exact Finset.subset_union_right)
  have hw₁₀ : w₁ 0 = w₀ 0 := Subtype.ext (hw₁0.trans hw₀0.symm)
  have hw₂₀ : w₂ 0 = w₀ n₀ := Subtype.ext (hw₂0.trans hw₀n.symm)
  have hedge : ∀ {w w' : Section34VertexIndex 𝒦 𝒦'}, w ≠ w' → ∀ z ∈ V w, z ∈ V w' →
      ∃ e' : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e'.1 ∧ w'.1 ⊆ e'.1 := by
    intro w w' hww z hz hz'
    obtain ⟨e', he'⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁.injOn hww hz hz'
    exact ⟨e', hcut.subset_of_mem_splitDiskImage hf₁.injOn he' hz,
      hcut.subset_of_mem_splitDiskImage hf₁.injOn he' hz'⟩
  have hrigid : ∀ {u v : Ea}, u ∈ t → v ∈ t → ∀ {w w' : Section34VertexIndex 𝒦 𝒦'}
      {p q : Ea}, w.1 = {p} → w'.1 = {q} → p ∈ segment ℝ u v → p ≠ u → p ≠ v →
      q ∈ convexHull ℝ (t : Set Ea) → p ≠ q → ∀ e' : Section34EdgeIndex 𝒦 𝒦',
      w.1 ⊆ e'.1 → w'.1 ⊆ e'.1 → q ∈ segment ℝ u v := by
    intro u v hu hv w w' p q hwp hwq hp hpu hpv hqt hpq e' hwe hwe'
    exact hcut.mem_segment_of_mem_segment_of_ne_of_incident ht hu hv hp hpu hpv e'
      (hsing e' hwp hwe) (hsing e' hwq hwe')
      (hinc e' p q hpq (hsing e' hwp hwe) (hsing e' hwq hwe')
        (hsegt hu hv hp) hqt)
  have hne : ∀ {w w' : Section34VertexIndex 𝒦 𝒦'} {p q : Ea}, w.1 = {p} →
      w'.1 = {q} → p ≠ q → w ≠ w' := by
    intro w w' p q hwp hwq hpq h
    have h' := congrArg Subtype.val h
    rw [hwp, hwq] at h'
    exact hpq (Finset.singleton_injective h')
  obtain ⟨B₀, hB₀⟩ : ∃ B, B = V (w₀ 0) ∪ ⋃ j ∈ Finset.range n₀, V (w₀ (j + 1)) := ⟨_, rfl⟩
  have hB₀mem : ∀ z ∈ B₀, ∃ i ≤ n₀, z ∈ V (w₀ i) := by
    intro z hz
    rw [hB₀] at hz
    rcases (hmemU _ (fun i => V (w₀ i)) _ _).mp hz with hz | ⟨j, -, hj, hz⟩
    · exact ⟨0, Nat.zero_le _, hz⟩
    · exact ⟨j, hj, hz⟩
  have hB₀sub : ∀ i ≤ n₀, V (w₀ i) ⊆ B₀ := by
    intro i hi z hz
    rw [hB₀]
    refine (hmemU _ (fun i => V (w₀ i)) _ _).mpr ?_
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact Or.inl hz
    · exact Or.inr ⟨i, hi0, hi, hz⟩
  have hB₀c : B₀ ⊆ c.source := by
    intro z hz
    obtain ⟨i, hi, hzi⟩ := hB₀mem z hz
    exact hW₀c i hi hzi
  have hB₀ball : IsPLCellOn 3 B₀ (frontier B₀) := by
    rw [hB₀]
    refine IsPLCellOn.union_biUnion_range_of_attach_in_chart (W := fun i => V (w₀ i))
      (WBd := fun i => section34VertexBallImage srcBd f₁ (w₀ i))
      (S := fun i => section34SplitDiskImage src f₁ (e₀ i)) (hVball _) n₀
      (fun i _ => hVball _) (fun i _ => hEball (e₀ i))
      (fun i hi => hfront (he₀ i hi)) (fun j hj => ?_) hc
      (hW₀c 0 (Nat.zero_le _)) (fun i hi => hW₀c (i + 1) hi)
    refine hcut.path_attach_meet hf₁ le_rfl he₀ hw₀inj hw₀far (fun z hz => hz.1)
      (fun j' _ hj' => hcut.disjoint_vertexBallImage_of_forall_not_subset hf₁
        (fun h => absurd (hw₀inj 0 (Nat.zero_le _) (j' + 1) (by omega) h) (by omega))
        (hw₀far 0 (Nat.zero_le _) (j' + 1) (by omega) (by omega))) subset_rfl hj
  have hopen₁ : ∀ j, 0 < j → j < n₁ → ∀ i ≤ n₀, ∀ z ∈ V (w₀ i), z ∈ V (w₁ j) →
      i = 0 ∧ j = 1 := by
    intro j hj0 hjn i hi z hz hz'
    obtain ⟨q, hq, hwq, hqo⟩ := hw₁pt j hjn.le
    obtain ⟨hqx, hqx'⟩ := hqo hj0 hjn
    obtain ⟨p, hp, hwp, -⟩ := hw₀pt i hi
    have hpq : q ≠ p := by
      rintro rfl
      exact hqx (mem_singleton_iff.mp (hmeet2 hx hy hx' hyx' ⟨hp, hq⟩))
    obtain ⟨e', hje, hie⟩ := hedge (hne hwq hwp hpq) z hz' hz
    have hpseg := hrigid hx hx' hwq hwp hq hqx hqx' (hsegt hx hy hp) hpq e' hje hie
    have hpx : p = x := mem_singleton_iff.mp (hmeet2 hx hy hx' hyx' ⟨hp, hpseg⟩)
    have hi0 : w₀ i = w₀ 0 := Subtype.ext (by rw [hwp, hw₀0, hpx])
    refine ⟨hw₀inj i hi 0 (Nat.zero_le _) hi0, ?_⟩
    by_contra hj1
    rw [hi0, ← hw₁₀] at hie
    exact hw₁far 0 (Nat.zero_le _) j hjn.le (by omega) e' hie hje
  have hopen₂ : ∀ j, 0 < j → j < n₂ → ∀ i ≤ n₀, ∀ z ∈ V (w₀ i), z ∈ V (w₂ j) →
      i = n₀ ∧ j = 1 := by
    intro j hj0 hjn i hi z hz hz'
    obtain ⟨q, hq, hwq, hqo⟩ := hw₂pt j hjn.le
    obtain ⟨hqy, hqy'⟩ := hqo hj0 hjn
    obtain ⟨p, hp, hwp, -⟩ := hw₀pt i hi
    have hp' : p ∈ segment ℝ y x := by
      rw [segment_symm]
      exact hp
    have hpq : q ≠ p := by
      rintro rfl
      exact hqy (mem_singleton_iff.mp (hmeet2 hy hy' hx (Ne.symm hxy') ⟨hq, hp'⟩))
    obtain ⟨e', hje, hie⟩ := hedge (hne hwq hwp hpq) z hz' hz
    have hpseg := hrigid hy hy' hwq hwp hq hqy hqy' (hsegt hx hy hp) hpq e' hje hie
    have hpy : p = y := mem_singleton_iff.mp (hmeet2 hy hy' hx (Ne.symm hxy') ⟨hpseg, hp'⟩)
    have hin : w₀ i = w₀ n₀ := Subtype.ext (by rw [hwp, hw₀n, hpy])
    refine ⟨hw₀inj i hi n₀ le_rfl hin, ?_⟩
    by_contra hj1
    rw [hin, ← hw₂₀] at hie
    exact hw₂far 0 (Nat.zero_le _) j hjn.le (by omega) e' hie hje
  have hopen₁₂ : ∀ j, 0 < j → j < n₁ → ∀ l, 0 < l → l < n₂ →
      Disjoint (V (w₁ j)) (V (w₂ l)) := by
    intro j _ hjn l hl0 hln
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    obtain ⟨p, hp, hwp, -⟩ := hw₁pt j hjn.le
    obtain ⟨q, hq, hwq, hqo⟩ := hw₂pt l hln.le
    obtain ⟨hqy, hqy'⟩ := hqo hl0 hln
    have hdis := hmeet0 hx hx' hy hy' hxy hxy' hyx'.symm hx'y'
    have hpq : q ≠ p := by
      rintro rfl
      exact Set.disjoint_left.mp hdis hp hq
    obtain ⟨e', hle, hje⟩ := hedge (hne hwq hwp hpq) z hz' hz
    have hpseg := hrigid hy hy' hwq hwp hq hqy hqy' (hsegt hx hx' hp) hpq e' hle hje
    exact Set.disjoint_left.mp hdis hp hpseg
  obtain ⟨B₁, hB₁⟩ : ∃ B, B = B₀ ∪ ⋃ j ∈ Finset.range (n₁ - 1), V (w₁ (j + 1)) :=
    ⟨_, rfl⟩
  have hB₁mem : ∀ z ∈ B₁, (∃ i ≤ n₀, z ∈ V (w₀ i)) ∨
      ∃ j, 0 < j ∧ j < n₁ ∧ z ∈ V (w₁ j) := by
    intro z hz
    rw [hB₁] at hz
    rcases (hmemU _ (fun i => V (w₁ i)) _ _).mp hz with hz | ⟨j, hj0, hj, hz⟩
    · exact Or.inl (hB₀mem z hz)
    · exact Or.inr ⟨j, hj0, by omega, hz⟩
  have hB₁sub₀ : B₀ ⊆ B₁ := by
    rw [hB₁]
    exact subset_union_left
  have hB₁sub : ∀ j, 0 < j → j < n₁ → V (w₁ j) ⊆ B₁ := by
    intro j hj0 hjn z hz
    rw [hB₁]
    exact (hmemU _ (fun i => V (w₁ i)) _ _).mpr (Or.inr ⟨j, hj0, by omega, hz⟩)
  have hB₁c : B₁ ⊆ c.source := by
    intro z hz
    rcases hB₁mem z hz with ⟨i, hi, hzi⟩ | ⟨j, -, hj, hzj⟩
    · exact hW₀c i hi hzi
    · exact hW₁c j hj.le hzj
  have hB₁ball : IsPLCellOn 3 B₁ (frontier B₁) := by
    rw [hB₁]
    refine IsPLCellOn.union_biUnion_range_of_attach_in_chart (W := fun i => V (w₁ i))
      (WBd := fun i => section34VertexBallImage srcBd f₁ (w₁ i))
      (S := fun i => section34SplitDiskImage src f₁ (e₁ i)) hB₀ball (n₁ - 1)
      (fun i _ => hVball _) (fun i _ => hEball (e₁ i))
      (fun i hi => hfront (he₁ i (by omega))) (fun j hj => ?_) hc
      hB₀c (fun i hi => hW₁c (i + 1) (by omega))
    refine hcut.path_attach_meet hf₁ (Nat.sub_le n₁ 1) he₁ hw₁inj hw₁far ?_ ?_ ?_ hj
    · rintro z ⟨hz, hz'⟩
      obtain ⟨i, hi, hzi⟩ := hB₀mem z hz
      obtain ⟨hi0, -⟩ := hopen₁ 1 one_pos (by omega) i hi z hzi hz'
      subst hi0
      rw [hw₁₀]
      exact hzi
    · intro j' hj'0 hj'
      refine Set.disjoint_left.mpr fun z hz hz' => ?_
      obtain ⟨i, hi, hzi⟩ := hB₀mem z hz
      obtain ⟨-, hj1⟩ := hopen₁ (j' + 1) (by omega) (by omega) i hi z hzi hz'
      omega
    · rw [hw₁₀]
      exact hB₀sub 0 (Nat.zero_le _)
  obtain ⟨B₂, hB₂⟩ : ∃ B, B = B₁ ∪ ⋃ j ∈ Finset.range (n₂ - 1), V (w₂ (j + 1)) :=
    ⟨_, rfl⟩
  have hB₂mem : ∀ z ∈ B₂, (∃ i ≤ n₀, z ∈ V (w₀ i)) ∨
      (∃ j, 0 < j ∧ j < n₁ ∧ z ∈ V (w₁ j)) ∨ ∃ j, 0 < j ∧ j < n₂ ∧ z ∈ V (w₂ j) := by
    intro z hz
    rw [hB₂] at hz
    rcases (hmemU _ (fun i => V (w₂ i)) _ _).mp hz with hz | ⟨j, hj0, hj, hz⟩
    · rcases hB₁mem z hz with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨j, hj0, by omega, hz⟩)
  have hB₂sub₁ : B₁ ⊆ B₂ := by
    rw [hB₂]
    exact subset_union_left
  have hB₂sub : ∀ j, 0 < j → j < n₂ → V (w₂ j) ⊆ B₂ := by
    intro j hj0 hjn z hz
    rw [hB₂]
    exact (hmemU _ (fun i => V (w₂ i)) _ _).mpr (Or.inr ⟨j, hj0, by omega, hz⟩)
  have hB₂ball : IsPLCellOn 3 B₂ (frontier B₂) := by
    rw [hB₂]
    refine IsPLCellOn.union_biUnion_range_of_attach_in_chart (W := fun i => V (w₂ i))
      (WBd := fun i => section34VertexBallImage srcBd f₁ (w₂ i))
      (S := fun i => section34SplitDiskImage src f₁ (e₂ i)) hB₁ball (n₂ - 1)
      (fun i _ => hVball _) (fun i _ => hEball (e₂ i))
      (fun i hi => hfront (he₂ i (by omega))) (fun j hj => ?_) hc
      hB₁c (fun i hi => hW₂c (i + 1) (by omega))
    refine hcut.path_attach_meet hf₁ (Nat.sub_le n₂ 1) he₂ hw₂inj hw₂far ?_ ?_ ?_ hj
    · rintro z ⟨hz, hz'⟩
      rcases hB₁mem z hz with ⟨i, hi, hzi⟩ | ⟨j', hj'0, hj'n, hzj'⟩
      · obtain ⟨hin, -⟩ := hopen₂ 1 one_pos (by omega) i hi z hzi hz'
        rw [hw₂₀, ← hin]
        exact hzi
      · exact absurd hz' (Set.disjoint_left.mp (hopen₁₂ j' hj'0 hj'n 1 one_pos (by omega)) hzj')
    · intro j' hj'0 hj'
      refine Set.disjoint_left.mpr fun z hz hz' => ?_
      rcases hB₁mem z hz with ⟨i, hi, hzi⟩ | ⟨j'', hj''0, hj''n, hzj''⟩
      · obtain ⟨-, hj1⟩ := hopen₂ (j' + 1) (by omega) (by omega) i hi z hzi hz'
        omega
      · exact Set.disjoint_left.mp (hopen₁₂ j'' hj''0 hj''n (j' + 1) (by omega) (by omega))
          hzj'' hz'
    · rw [hw₂₀]
      exact (hB₀sub n₀ le_rfl).trans hB₁sub₀
  have hclaw : section34ClawBall V x y x' y' = B₂ := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨w, ⟨p, hwp, hp⟩, hzw⟩ := mem_iUnion₂.mp hz
      rcases hp with hp | ⟨hp, hpx'⟩ | ⟨hp, hpy'⟩
      · obtain ⟨i, hi, rfl⟩ := hw₀surj w ⟨p, hp, hwp⟩
        exact hB₂sub₁ (hB₁sub₀ (hB₀sub i hi hzw))
      · obtain ⟨i, hi, rfl⟩ := hw₁surj w ⟨p, hp, hwp⟩
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [hw₁₀] at hzw
          exact hB₂sub₁ (hB₁sub₀ (hB₀sub 0 (Nat.zero_le _) hzw))
        · have hin : i ≠ n₁ := by
            rintro rfl
            rw [hw₁n] at hwp
            exact hpx' (Finset.singleton_injective hwp).symm
          exact hB₂sub₁ (hB₁sub i hi0 (by omega) hzw)
      · obtain ⟨i, hi, rfl⟩ := hw₂surj w ⟨p, hp, hwp⟩
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rw [hw₂₀] at hzw
          exact hB₂sub₁ (hB₁sub₀ (hB₀sub n₀ le_rfl hzw))
        · have hin : i ≠ n₂ := by
            rintro rfl
            rw [hw₂n] at hwp
            exact hpy' (Finset.singleton_injective hwp).symm
          exact hB₂sub i hi0 (by omega) hzw
    · have hsubclaw : ∀ (w : Section34VertexIndex 𝒦 𝒦') (p : Ea), w.1 = {p} →
          (p ∈ segment ℝ x y ∨ (p ∈ segment ℝ x x' ∧ p ≠ x') ∨
            (p ∈ segment ℝ y y' ∧ p ≠ y')) → V w ⊆ section34ClawBall V x y x' y' :=
        fun w p hwp hp z hz => mem_iUnion₂.mpr ⟨w, ⟨p, hwp, hp⟩, hz⟩
      intro z hz
      rcases hB₂mem z hz with ⟨i, hi, hzi⟩ | ⟨j, hj0, hjn, hzj⟩ | ⟨j, hj0, hjn, hzj⟩
      · obtain ⟨p, hp, hwp, -⟩ := hw₀pt i hi
        exact hsubclaw _ p hwp (Or.inl hp) hzi
      · obtain ⟨p, hp, hwp, hpo⟩ := hw₁pt j hjn.le
        exact hsubclaw _ p hwp (Or.inr (Or.inl ⟨hp, (hpo hj0 hjn).2⟩)) hzj
      · obtain ⟨p, hp, hwp, hpo⟩ := hw₂pt j hjn.le
        exact hsubclaw _ p hwp (Or.inr (Or.inr ⟨hp, (hpo hj0 hjn).2⟩)) hzj
  rw [hclaw]
  exact hB₂ball

end DifferentialGeometry.Topology.PiecewiseLinear
