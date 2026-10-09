/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTetraCircle
import DifferentialGeometry.Topology.PiecewiseLinear.TwoBallPocket
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnEndpoints

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}
  {fblBd tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set E3}
  {tgtA tgtABd : Section34CompactArcIndex K K' → Set E3}
  {tgtP : Section34CompactMarkIndex K K' → Set E3}

theorem section34Incident_of_subset_segment {e s : Finset E3} {u v : E3}
    (he : convexHull ℝ (e : Set E3) ⊆ segment ℝ u v) (hu : u ∈ s) (hv : v ∈ s) :
    Section34Incident e s := fun _ hz =>
  (convex_convexHull ℝ _).segment_subset (subset_convexHull ℝ _ hu) (subset_convexHull ℝ _ hv)
    (he (subset_convexHull ℝ _ hz))

theorem not_section34Incident_of_notMem_left {e s : Finset E3} (hs : s ∈ K.faces) {u : E3}
    (huK : ({u} : Finset E3) ∈ K.faces) (hue : u ∈ e) (hus : u ∉ s) :
    ¬ Section34Incident e s := by
  classical
  intro h
  have hu : u ∈ convexHull ℝ (s : Set E3) := h (Finset.mem_coe.mpr hue)
  have h' := K.inter_subset_convexHull huK hs
    ⟨subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_singleton_self u)), hu⟩
  rw [← Finset.coe_inter, Finset.singleton_inter_of_notMem hus, Finset.coe_empty,
    convexHull_empty] at h'
  exact h'

theorem not_section34Incident_of_notMem_right {e s : Finset E3} (hs : s ∈ K.faces)
    {u v x : E3} (huv : ({u, v} : Finset E3) ∈ K.faces) (hx : x ∈ e) (hxseg : x ∈ segment ℝ u v)
    (hxu : x ≠ u) (hvs : v ∉ s) : ¬ Section34Incident e s := by
  classical
  intro h
  have hxs : x ∈ convexHull ℝ (s : Set E3) := h (Finset.mem_coe.mpr hx)
  have h' := mem_convexHull_inter_of_mem_segment hs huv hxseg hxs
  have hsub : (({u, v} : Finset E3) ∩ s : Finset E3) ⊆ {u} := by
    intro z hz
    rw [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with ⟨hz | hz, hzs⟩
    · exact Finset.mem_singleton.mpr hz
    · rw [hz] at hzs
      exact absurd hzs hvs
  have h'' := convexHull_mono (Finset.coe_subset.mpr hsub) h'
  rw [Finset.coe_singleton, convexHull_singleton] at h''
  exact hxu h''

theorem Section34CompactFaceDiskFamily.exists_faceDisk_inter_splitDiskImage_eq_singleton
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (s : Section34CompactSimplexIndex K 3) (e : Section34CompactEdgeIndex K K')
    (hse : Section34Incident e.1 s.1) :
    ∃ P : E3, tgtD s ∩ section34CompactSplitDiskImage src f₁ e = {P} ∧
      P ∈ section34CompactSplitDiskImage srcBd f₁ e := by
  have heq := hdisk.faceDisk_inter_splitDiskImage_eq hcut hf₁ ⟨(s, e), hse⟩
  obtain ⟨-, -, -, -, -, -, -, -, hP9, hP10, -⟩ := hdisk
  obtain ⟨P, hP⟩ := (hP9 ⟨(s, e), hse⟩).exists_eq_singleton
  refine ⟨P, heq.trans hP, ?_⟩
  have hPm : P ∈ tgtP ⟨(s, e), hse⟩ := by
    rw [hP]
    exact mem_singleton P
  rw [← hP10 ⟨(s, e), hse⟩] at hPm
  exact hPm.2

theorem Section34CompactFaceDiskFamily.exists_runs_of_face
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {B₁ B₂ : Set E3} (hB₁ : IsClosed B₁) (hB₂ : IsClosed B₂)
    (hsub : B₁ ∪ B₂ ⊆ ⋃ w, section34CompactVertexBallImage src f₁ w)
    {eH : Fin 4 → Section34CompactEdgeIndex K K'}
    (h12 : B₁ ∩ B₂ = ⋃ k, section34CompactSplitDiskImage src f₁ (eH k))
    (s : Section34CompactSimplexIndex K 3)
    (hcov : ∀ w : Section34CompactVertexIndex K K', Section34Incident w.1 s.1 →
      section34CompactVertexBallImage src f₁ w ⊆ B₁ ∪ B₂)
    {i j : Fin 4} (hij : eH i ≠ eH j) (hsi : Section34Incident (eH i).1 s.1)
    (hsj : Section34Incident (eH j).1 s.1)
    (hso : ∀ k, k ≠ i → k ≠ j → ¬ Section34Incident (eH k).1 s.1)
    {w₁ w₂ : Section34CompactVertexIndex K K'} (hw₁ : Section34Incident w₁.1 s.1)
    (hw₂ : Section34Incident w₂.1 s.1) (hV₁ : section34CompactVertexBallImage src f₁ w₁ ⊆ B₁)
    (hV₂ : section34CompactVertexBallImage src f₁ w₂ ⊆ B₂) :
    ∃ p q : E3, p ∈ section34CompactSplitDiskImage srcBd f₁ (eH i) ∧
      q ∈ section34CompactSplitDiskImage srcBd f₁ (eH j) ∧
      tgtD s ∩ section34CompactSplitDiskImage src f₁ (eH i) = {p} ∧
      tgtD s ∩ section34CompactSplitDiskImage src f₁ (eH j) = {q} ∧
      (∀ k, k ≠ i → k ≠ j → tgtD s ∩ section34CompactSplitDiskImage src f₁ (eH k) = ∅) ∧
      tgtDBd s = tgtD s ∩ B₁ ∪ tgtD s ∩ B₂ ∧ tgtD s ∩ B₁ ∩ (tgtD s ∩ B₂) = {p, q} ∧
      (∃ γ₁ : ℝ → E3, IsPLHomeomorphOn γ₁ (Icc 0 1) (tgtD s ∩ B₁) ∧ γ₁ 0 = p ∧ γ₁ 1 = q) ∧
      ∃ γ₂ : ℝ → E3, IsPLHomeomorphOn γ₂ (Icc 0 1) (tgtD s ∩ B₂) ∧ γ₂ 0 = p ∧ γ₂ 1 = q := by
  obtain ⟨p, hp, hpb⟩ := hdisk.exists_faceDisk_inter_splitDiskImage_eq_singleton hcut hf₁ s _ hsi
  obtain ⟨q, hq, hqb⟩ := hdisk.exists_faceDisk_inter_splitDiskImage_eq_singleton hcut hf₁ s _ hsj
  have hso' : ∀ k, k ≠ i → k ≠ j →
      tgtD s ∩ section34CompactSplitDiskImage src f₁ (eH k) = ∅ := fun k hki hkj =>
    hdisk.faceDisk_inter_splitDiskImage_eq_empty hcut hf₁ (hso k hki hkj)
  obtain ⟨-, hDb, hinter, hγ₁, hγ₂⟩ := hdisk.exists_arcs_of_holes hB₁ hB₂ hsub
    (fun k => ⟨eH k, rfl⟩) h12 s hcov hp hq (hcut.disjoint_splitDiskImage hf₁ hij) hso' hw₁ hw₂
    hV₁ hV₂
  exact ⟨p, q, hpb, hqb, hp, hq, hso', hDb, hinter, hγ₁, hγ₂⟩

theorem Section34CompactCutFrame.clawBall_holes
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {t : Finset E3} (ht : t ∈ K.faces) {a b c d : E3} (htabcd : t = {a, b, c, d})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {ea eb ec ed : Section34CompactEdgeIndex K K'}
    (hea₁ : a ∈ ea.1) (hea₂ : convexHull ℝ (ea.1 : Set E3) ⊆ segment ℝ a d)
    (hea : ∀ e : Section34CompactEdgeIndex K K', a ∈ e.1 →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ a d → e = ea)
    (heb₁ : b ∈ eb.1) (heb₂ : convexHull ℝ (eb.1 : Set E3) ⊆ segment ℝ b c)
    (heb : ∀ e : Section34CompactEdgeIndex K K', b ∈ e.1 →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ b c → e = eb)
    (hec₁ : c ∈ ec.1) (hec₂ : convexHull ℝ (ec.1 : Set E3) ⊆ segment ℝ c a)
    (hec : ∀ e : Section34CompactEdgeIndex K K', c ∈ e.1 →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ c a → e = ec)
    (hed₁ : d ∈ ed.1) (hed₂ : convexHull ℝ (ed.1 : Set E3) ⊆ segment ℝ d b)
    (hed : ∀ e : Section34CompactEdgeIndex K K', d ∈ e.1 →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ d b → e = ed) :
    (∀ k l : Fin 4, k ≠ l → ![ec, eb, ed, ea] k ≠ ![ec, eb, ed, ea] l) ∧
      section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d ∩
          section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b =
        ⋃ k, section34CompactSplitDiskImage src f₁ (![ec, eb, ed, ea] k) ∧
      (∀ k, section34CompactSplitDiskImage src f₁ (![ec, eb, ed, ea] k) ⊆
        frontier (section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d)) ∧
      (∀ k, section34CompactSplitDiskImage src f₁ (![ec, eb, ed, ea] k) ⊆
        frontier (section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b)) ∧
      ∀ k, section34CompactSplitDiskImage src f₁ (![ec, eb, ed, ea] k) \
          section34CompactSplitDiskImage srcBd f₁ (![ec, eb, ed, ea] k) ⊆
        interior (section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d ∪
          section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b) := by
  have ha : a ∈ t := by rw [htabcd]; simp
  have hb : b ∈ t := by rw [htabcd]; simp
  have hc : c ∈ t := by rw [htabcd]; simp
  have hd : d ∈ t := by rw [htabcd]; simp
  have hseg : ∀ {e : Section34CompactEdgeIndex K K'} {u v x : E3},
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ u v → x ∈ e.1 → x ∈ segment ℝ u v :=
    fun he hx => he (subset_convexHull ℝ _ hx)
  have hsymm : ∀ {u v x : E3}, x ∈ segment ℝ u v → x ∈ segment ℝ v u := fun h => by
    rwa [segment_symm]
  obtain ⟨wa, wa', pa, hwa, hwa', hpae, hpaa, hwae, hwa'e⟩ :=
    exists_vertexIndex_pair_of_mem_edgeIndex ea hea₁
  obtain ⟨wb, wb', pb, hwb, hwb', hpbe, hpbb, hwbe, hwb'e⟩ :=
    exists_vertexIndex_pair_of_mem_edgeIndex eb heb₁
  obtain ⟨wc, wc', pc, hwc, hwc', hpce, hpcc, hwce, hwc'e⟩ :=
    exists_vertexIndex_pair_of_mem_edgeIndex ec hec₁
  obtain ⟨wd, wd', pd, hwd, hwd', hpde, hpdd, hwde, hwd'e⟩ :=
    exists_vertexIndex_pair_of_mem_edgeIndex ed hed₁
  have hA := hcut.splitDiskImage_subset_frontier_clawBall hf₁ ht ha hb hc hd hab hac had hbc
    hbd hcd hwa hwa' (Or.inl (left_mem_segment ℝ a b))
    (Or.inr (Or.inl ⟨hsymm (hseg hea₂ hpae), hpaa⟩)) hwae hwa'e
  have hB := hcut.splitDiskImage_subset_frontier_clawBall hf₁ ht ha hb hc hd hab hac had hbc
    hbd hcd hwb hwb' (Or.inl (right_mem_segment ℝ a b))
    (Or.inr (Or.inr ⟨hsymm (hseg heb₂ hpbe), hpbb⟩)) hwbe hwb'e
  have hC := hcut.splitDiskImage_subset_frontier_clawBall hf₁ ht ha hb hc hd hab hac had hbc
    hbd hcd hwc' hwc (Or.inr (Or.inl ⟨hsymm (hseg hec₂ hpce), hpcc⟩))
    (Or.inl (right_mem_segment ℝ d c)) hwc'e hwce
  have hD := hcut.splitDiskImage_subset_frontier_clawBall hf₁ ht ha hb hc hd hab hac had hbc
    hbd hcd hwd' hwd (Or.inr (Or.inr ⟨hsymm (hseg hed₂ hpde), hpdd⟩))
    (Or.inl (left_mem_segment ℝ d c)) hwd'e hwde
  have hone : ∀ {u v w x : E3}, u ∈ t → v ∈ t → w ∈ t → v ≠ w → x ∈ segment ℝ u v →
      x ∈ segment ℝ u w → x = u := fun hu hv hw hvw h h' =>
    mem_singleton_iff.mp (segment_inter_segment_subset_singleton_of_mem_faces ht hu hv hw hvw
      ⟨h, h'⟩)
  have hab' : ea ≠ eb := by
    intro h
    have h1 : a ∈ segment ℝ b c := hseg heb₂ (by rw [← h]; exact hea₁)
    exact Set.disjoint_left.mp (disjoint_segment_segment_of_mem_faces ht ha hd hb hc hab hac
      hbd.symm hcd.symm) (left_mem_segment ℝ a d) h1
  have hac' : ea ≠ ec := by
    intro h
    have h1 : c ∈ segment ℝ a d := hseg hea₂ (by rw [h]; exact hec₁)
    exact hac (hone ha hd hc hcd.symm h1 (right_mem_segment ℝ a c)).symm
  have had' : ea ≠ ed := by
    intro h
    have h1 : a ∈ segment ℝ d b := hseg hed₂ (by rw [← h]; exact hea₁)
    exact had (hone hd hb ha hab.symm h1 (right_mem_segment ℝ d a))
  have hbc' : eb ≠ ec := by
    intro h
    have h1 : b ∈ segment ℝ c a := hseg hec₂ (by rw [← h]; exact heb₁)
    exact hbc (hone hc ha hb hab h1 (right_mem_segment ℝ c b))
  have hbd' : eb ≠ ed := by
    intro h
    have h1 : d ∈ segment ℝ b c := hseg heb₂ (by rw [h]; exact hed₁)
    exact hbd (hone hb hc hd hcd h1 (right_mem_segment ℝ b d)).symm
  have hcd' : ec ≠ ed := by
    intro h
    have h1 : c ∈ segment ℝ d b := hseg hed₂ (by rw [← h]; exact hec₁)
    exact Set.disjoint_left.mp (disjoint_segment_segment_of_mem_faces ht hc ha hd hb hcd
      hbc.symm had hab) (left_mem_segment ℝ c a) h1
  have hsubU := hcut.clawBall_inter_clawBall hf₁ ht htabcd hab hac had hbc hbd hcd hea heb hec hed
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k l hkl
    fin_cases k <;> fin_cases l
    all_goals first
      | exact absurd rfl hkl
      | exact hbc' | exact hbc'.symm | exact hcd' | exact hcd'.symm | exact hac' | exact hac'.symm
      | exact hbd' | exact hbd'.symm | exact hab' | exact hab'.symm | exact had' | exact had'.symm
  · apply Subset.antisymm
    · intro z hz
      rcases hsubU hz with ((h | h) | h) | h
      · exact mem_iUnion.mpr ⟨3, h⟩
      · exact mem_iUnion.mpr ⟨1, h⟩
      · exact mem_iUnion.mpr ⟨0, h⟩
      · exact mem_iUnion.mpr ⟨2, h⟩
    · refine iUnion_subset fun k => ?_
      fin_cases k
      exacts [hC.1, hB.1, hD.1, hA.1]
  · intro k
    fin_cases k
    exacts [hC.2.1, hB.2.1, hD.2.1, hA.2.1]
  · intro k
    fin_cases k
    exacts [hC.2.2.1, hB.2.2.1, hD.2.2.1, hA.2.2.1]
  · intro k
    fin_cases k
    exacts [hC.2.2.2, hB.2.2.2, hD.2.2.2, hA.2.2.2]

theorem Section34CompactFaceDiskFamily.exists_faceRuns_of_tetra
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Finset E3} (ht : t ∈ K.faces) {a b c d : E3} (htabcd : t = {a, b, c, d})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {ea eb ec ed : Section34CompactEdgeIndex K K'}
    (hea₁ : a ∈ ea.1) (hea₂ : convexHull ℝ (ea.1 : Set E3) ⊆ segment ℝ a d)
    (heb₁ : b ∈ eb.1) (heb₂ : convexHull ℝ (eb.1 : Set E3) ⊆ segment ℝ b c)
    (hec₁ : c ∈ ec.1) (hec₂ : convexHull ℝ (ec.1 : Set E3) ⊆ segment ℝ c a)
    (hed₁ : d ∈ ed.1) (hed₂ : convexHull ℝ (ed.1 : Set E3) ⊆ segment ℝ d b)
    (hinj : ∀ k l : Fin 4, k ≠ l → ![ec, eb, ed, ea] k ≠ ![ec, eb, ed, ea] l)
    (h12 : section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d ∩
        section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b =
      ⋃ k, section34CompactSplitDiskImage src f₁ (![ec, eb, ed, ea] k))
    {sacd sabc sbcd sabd : Section34CompactSimplexIndex K 3} (hsacd : sacd.1 = {a, c, d})
    (hsabc : sabc.1 = {a, b, c}) (hsbcd : sbcd.1 = {b, c, d}) (hsabd : sabd.1 = {a, b, d}) :
    ∃ (pin pout : Fin 4 → E3) (γ₁ γ₂ : Fin 4 → ℝ → E3),
      (∀ k, pin k ∈ section34CompactSplitDiskImage srcBd f₁ (![ec, eb, ed, ea] (k - 1))) ∧
      (∀ k, pout k ∈ section34CompactSplitDiskImage srcBd f₁ (![ec, eb, ed, ea] k)) ∧
      (∀ k, tgtD (![sacd, sabc, sbcd, sabd] k) ∩
        section34CompactSplitDiskImage src f₁ (![ec, eb, ed, ea] (k - 1)) = {pin k}) ∧
      (∀ k, tgtD (![sacd, sabc, sbcd, sabd] k) ∩
        section34CompactSplitDiskImage src f₁ (![ec, eb, ed, ea] k) = {pout k}) ∧
      (∀ k l, l ≠ k - 1 → l ≠ k → tgtD (![sacd, sabc, sbcd, sabd] k) ∩
        section34CompactSplitDiskImage src f₁ (![ec, eb, ed, ea] l) = ∅) ∧
      (∀ k, tgtDBd (![sacd, sabc, sbcd, sabd] k) =
        tgtD (![sacd, sabc, sbcd, sabd] k) ∩
            section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d ∪
          tgtD (![sacd, sabc, sbcd, sabd] k) ∩
            section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b) ∧
      (∀ k, tgtD (![sacd, sabc, sbcd, sabd] k) ∩
          section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d ∩
        (tgtD (![sacd, sabc, sbcd, sabd] k) ∩
          section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b) =
        {pin k, pout k}) ∧
      (∀ k, IsPLHomeomorphOn (γ₁ k) (Icc 0 1) (tgtD (![sacd, sabc, sbcd, sabd] k) ∩
          section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d) ∧
        γ₁ k 0 = pin k ∧ γ₁ k 1 = pout k) ∧
      ∀ k, IsPLHomeomorphOn (γ₂ k) (Icc 0 1) (tgtD (![sacd, sabc, sbcd, sabd] k) ∩
          section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b) ∧
        γ₂ k 0 = pin k ∧ γ₂ k 1 = pout k := by
  classical
  set V := section34CompactVertexBallImage src f₁
  set B₁ := section34CompactClawBall V a b c d
  set B₂ := section34CompactClawBall V d c a b
  have ha : a ∈ t := by rw [htabcd]; simp
  have hb : b ∈ t := by rw [htabcd]; simp
  have hc : c ∈ t := by rw [htabcd]; simp
  have hd : d ∈ t := by rw [htabcd]; simp
  have hvK : ∀ {u : E3}, u ∈ t → ({u} : Finset E3) ∈ K.faces := fun hu =>
    K.down_closed ht (Finset.singleton_subset_iff.mpr hu) (Finset.singleton_nonempty _)
  have hpK : ∀ {u v : E3}, u ∈ t → v ∈ t → ({u, v} : Finset E3) ∈ K.faces := fun hu hv =>
    K.down_closed ht (Finset.insert_subset hu (Finset.singleton_subset_iff.mpr hv))
      (Finset.insert_nonempty _ _)
  have hB₁c : IsClosed B₁ :=
    (hcut.isPLBall_section34CompactClawBall hf₁ ht ha hb hc hd hab hac hbd had hbc
      hcd).isPolyhedron.isClosed
  have hB₂c : IsClosed B₂ :=
    (hcut.isPLBall_section34CompactClawBall hf₁ ht hd hc ha hb hcd.symm had.symm hbc.symm
      hbd.symm hac.symm hab).isPolyhedron.isClosed
  have hsub : B₁ ∪ B₂ ⊆ ⋃ w, V w := by
    refine union_subset (iUnion₂_subset fun w _ => subset_iUnion V w)
      (iUnion₂_subset fun w _ => subset_iUnion V w)
  have hst : ∀ {s : Section34CompactSimplexIndex K 3}, (s.1 : Set E3) ⊆ t →
      ∀ w : Section34CompactVertexIndex K K', Section34Incident w.1 s.1 → V w ⊆ B₁ ∪ B₂ :=
    fun hs w hw => vertexBallImage_subset_clawBall_union ht htabcd
      (hw.trans (convexHull_min (hs.trans (subset_convexHull ℝ _)) (convex_convexHull ℝ _)))
  have hsubt : ∀ {s : Finset E3} {x y z : E3}, s = {x, y, z} → x ∈ t → y ∈ t → z ∈ t →
      (s : Set E3) ⊆ t := by
    intro s x y z hs hx hy hz u hu
    rw [hs] at hu
    simp only [Finset.coe_insert, Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hu
    rcases hu with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  obtain ⟨wa, wa', pa, hwa, -, hpae, hpaa, -, -⟩ := exists_vertexIndex_pair_of_mem_edgeIndex ea hea₁
  obtain ⟨wb, wb', pb, hwb, -, hpbe, hpbb, -, -⟩ := exists_vertexIndex_pair_of_mem_edgeIndex eb heb₁
  obtain ⟨wc, wc', pc, hwc, -, hpce, hpcc, -, -⟩ := exists_vertexIndex_pair_of_mem_edgeIndex ec hec₁
  obtain ⟨wd, wd', pd, hwd, -, hpde, hpdd, -, -⟩ := exists_vertexIndex_pair_of_mem_edgeIndex ed hed₁
  have hVa : V wa ⊆ B₁ := fun z hz =>
    mem_iUnion₂.mpr ⟨wa, ⟨a, hwa, Or.inl (left_mem_segment ℝ a b)⟩, hz⟩
  have hVb : V wb ⊆ B₁ := fun z hz =>
    mem_iUnion₂.mpr ⟨wb, ⟨b, hwb, Or.inl (right_mem_segment ℝ a b)⟩, hz⟩
  have hVc : V wc ⊆ B₂ := fun z hz =>
    mem_iUnion₂.mpr ⟨wc, ⟨c, hwc, Or.inl (right_mem_segment ℝ d c)⟩, hz⟩
  have hVd : V wd ⊆ B₂ := fun z hz =>
    mem_iUnion₂.mpr ⟨wd, ⟨d, hwd, Or.inl (left_mem_segment ℝ d c)⟩, hz⟩
  have hwinc : ∀ {w : Section34CompactVertexIndex K K'} {u : E3} {s : Finset E3}, w.1 = {u} →
      u ∈ s → Section34Incident w.1 s := by
    intro w u s hw hu z hz
    rw [hw, Finset.coe_singleton] at hz
    rw [mem_singleton_iff.mp hz]
    exact subset_convexHull ℝ _ (Finset.mem_coe.mpr hu)
  have hseg : ∀ {e : Section34CompactEdgeIndex K K'} {u v x : E3},
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ u v → x ∈ e.1 → x ∈ segment ℝ u v :=
    fun he hx => he (subset_convexHull ℝ _ hx)
  have hmem : ∀ {s : Finset E3} {x y z u : E3}, s = {x, y, z} → (u = x ∨ u = y ∨ u = z) →
      u ∈ s := by
    intro s x y z u hs hu
    rw [hs]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hu
  have hnmem : ∀ {s : Finset E3} {x y z u : E3}, s = {x, y, z} → u ≠ x → u ≠ y → u ≠ z →
      u ∉ s := by
    intro s x y z u hs hx hy hz hu
    rw [hs] at hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with h | h | h
    · exact hx h
    · exact hy h
    · exact hz h
  have hface : ∀ k : Fin 4, ∃ (p q : E3) (g₁ g₂ : ℝ → E3),
      p ∈ section34CompactSplitDiskImage srcBd f₁ (![ec, eb, ed, ea] (k - 1)) ∧
      q ∈ section34CompactSplitDiskImage srcBd f₁ (![ec, eb, ed, ea] k) ∧
      tgtD (![sacd, sabc, sbcd, sabd] k) ∩
        section34CompactSplitDiskImage src f₁ (![ec, eb, ed, ea] (k - 1)) = {p} ∧
      tgtD (![sacd, sabc, sbcd, sabd] k) ∩
        section34CompactSplitDiskImage src f₁ (![ec, eb, ed, ea] k) = {q} ∧
      (∀ l, l ≠ k - 1 → l ≠ k → tgtD (![sacd, sabc, sbcd, sabd] k) ∩
        section34CompactSplitDiskImage src f₁ (![ec, eb, ed, ea] l) = ∅) ∧
      tgtDBd (![sacd, sabc, sbcd, sabd] k) =
        tgtD (![sacd, sabc, sbcd, sabd] k) ∩ B₁ ∪ tgtD (![sacd, sabc, sbcd, sabd] k) ∩ B₂ ∧
      tgtD (![sacd, sabc, sbcd, sabd] k) ∩ B₁ ∩ (tgtD (![sacd, sabc, sbcd, sabd] k) ∩ B₂) =
        {p, q} ∧
      (IsPLHomeomorphOn g₁ (Icc 0 1) (tgtD (![sacd, sabc, sbcd, sabd] k) ∩ B₁) ∧
        g₁ 0 = p ∧ g₁ 1 = q) ∧
      (IsPLHomeomorphOn g₂ (Icc 0 1) (tgtD (![sacd, sabc, sbcd, sabd] k) ∩ B₂) ∧
        g₂ 0 = p ∧ g₂ 1 = q) := by
    intro k
    fin_cases k
    · obtain ⟨p, q, hp, hq, hDi, hDj, hDo, hDb, hint, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ :=
        hdisk.exists_runs_of_face hcut hf₁ hB₁c hB₂c hsub h12 sacd
          (hst (hsubt hsacd ha hc hd)) (i := 3) (j := 0) (hinj 3 0 (by decide))
          (section34Incident_of_subset_segment hea₂ (hmem hsacd (Or.inl rfl))
            (hmem hsacd (Or.inr (Or.inr rfl))))
          (section34Incident_of_subset_segment hec₂ (hmem hsacd (Or.inr (Or.inl rfl)))
            (hmem hsacd (Or.inl rfl)))
          (fun l h1 h2 => by
            fin_cases l
            · exact absurd rfl h2
            · exact not_section34Incident_of_notMem_left sacd.2.1 (hvK hb) heb₁
                (hnmem hsacd hab.symm hbc hbd)
            · exact not_section34Incident_of_notMem_right sacd.2.1 (hpK hd hb) hpde
                (hseg hed₂ hpde) hpdd (hnmem hsacd hab.symm hbc hbd)
            · exact absurd rfl h1)
          (hwinc hwa (hmem hsacd (Or.inl rfl))) (hwinc hwd (hmem hsacd (Or.inr (Or.inr rfl))))
          hVa hVd
      exact ⟨p, q, g₁, g₂, hp, hq, hDi, hDj, hDo, hDb, hint, hg₁, hg₂⟩
    · obtain ⟨p, q, hp, hq, hDi, hDj, hDo, hDb, hint, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ :=
        hdisk.exists_runs_of_face hcut hf₁ hB₁c hB₂c hsub h12 sabc
          (hst (hsubt hsabc ha hb hc)) (i := 0) (j := 1) (hinj 0 1 (by decide))
          (section34Incident_of_subset_segment hec₂ (hmem hsabc (Or.inr (Or.inr rfl)))
            (hmem hsabc (Or.inl rfl)))
          (section34Incident_of_subset_segment heb₂ (hmem hsabc (Or.inr (Or.inl rfl)))
            (hmem hsabc (Or.inr (Or.inr rfl))))
          (fun l h1 h2 => by
            fin_cases l
            · exact absurd rfl h1
            · exact absurd rfl h2
            · exact not_section34Incident_of_notMem_left sabc.2.1 (hvK hd) hed₁
                (hnmem hsabc had.symm hbd.symm hcd.symm)
            · exact not_section34Incident_of_notMem_right sabc.2.1 (hpK ha hd) hpae
                (hseg hea₂ hpae) hpaa (hnmem hsabc had.symm hbd.symm hcd.symm))
          (hwinc hwa (hmem hsabc (Or.inl rfl))) (hwinc hwc (hmem hsabc (Or.inr (Or.inr rfl))))
          hVa hVc
      exact ⟨p, q, g₁, g₂, hp, hq, hDi, hDj, hDo, hDb, hint, hg₁, hg₂⟩
    · obtain ⟨p, q, hp, hq, hDi, hDj, hDo, hDb, hint, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ :=
        hdisk.exists_runs_of_face hcut hf₁ hB₁c hB₂c hsub h12 sbcd
          (hst (hsubt hsbcd hb hc hd)) (i := 1) (j := 2) (hinj 1 2 (by decide))
          (section34Incident_of_subset_segment heb₂ (hmem hsbcd (Or.inl rfl))
            (hmem hsbcd (Or.inr (Or.inl rfl))))
          (section34Incident_of_subset_segment hed₂ (hmem hsbcd (Or.inr (Or.inr rfl)))
            (hmem hsbcd (Or.inl rfl)))
          (fun l h1 h2 => by
            fin_cases l
            · exact not_section34Incident_of_notMem_right sbcd.2.1 (hpK hc ha) hpce
                (hseg hec₂ hpce) hpcc (hnmem hsbcd hab hac had)
            · exact absurd rfl h1
            · exact absurd rfl h2
            · exact not_section34Incident_of_notMem_left sbcd.2.1 (hvK ha) hea₁
                (hnmem hsbcd hab hac had))
          (hwinc hwb (hmem hsbcd (Or.inl rfl))) (hwinc hwc (hmem hsbcd (Or.inr (Or.inl rfl))))
          hVb hVc
      exact ⟨p, q, g₁, g₂, hp, hq, hDi, hDj, hDo, hDb, hint, hg₁, hg₂⟩
    · obtain ⟨p, q, hp, hq, hDi, hDj, hDo, hDb, hint, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ :=
        hdisk.exists_runs_of_face hcut hf₁ hB₁c hB₂c hsub h12 sabd
          (hst (hsubt hsabd ha hb hd)) (i := 2) (j := 3) (hinj 2 3 (by decide))
          (section34Incident_of_subset_segment hed₂ (hmem hsabd (Or.inr (Or.inr rfl)))
            (hmem hsabd (Or.inr (Or.inl rfl))))
          (section34Incident_of_subset_segment hea₂ (hmem hsabd (Or.inl rfl))
            (hmem hsabd (Or.inr (Or.inr rfl))))
          (fun l h1 h2 => by
            fin_cases l
            · exact not_section34Incident_of_notMem_left sabd.2.1 (hvK hc) hec₁
                (hnmem hsabd hac.symm hbc.symm hcd)
            · exact not_section34Incident_of_notMem_right sabd.2.1 (hpK hb hc) hpbe
                (hseg heb₂ hpbe) hpbb (hnmem hsabd hac.symm hbc.symm hcd)
            · exact absurd rfl h1
            · exact absurd rfl h2)
          (hwinc hwa (hmem hsabd (Or.inl rfl))) (hwinc hwd (hmem hsabd (Or.inr (Or.inr rfl))))
          hVa hVd
      exact ⟨p, q, g₁, g₂, hp, hq, hDi, hDj, hDo, hDb, hint, hg₁, hg₂⟩
  choose pin pout γ₁ γ₂ hp hq hDi hDj hDo hDb hint hg₁ hg₂ using hface
  exact ⟨pin, pout, γ₁, γ₂, hp, hq, hDi, hDj, hDo, hDb, hint, hg₁, hg₂⟩

theorem iUnion_fin_four (f : Fin 4 → Set E3) : ⋃ k, f k = f 0 ∪ f 1 ∪ f 2 ∪ f 3 := by
  ext z
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨k, hk⟩
    fin_cases k
    · exact Or.inl (Or.inl (Or.inl hk))
    · exact Or.inl (Or.inl (Or.inr hk))
    · exact Or.inl (Or.inr hk)
    · exact Or.inr hk
  · rintro (((h | h) | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩

theorem Section34CompactCutFrame.exists_isPLBall_of_tetra
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Finset E3} (ht : t ∈ K.faces) {a b c d : E3} (htabcd : t = {a, b, c, d})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {ea eb ec ed : Section34CompactEdgeIndex K K'}
    (hea₁ : a ∈ ea.1) (hea₂ : convexHull ℝ (ea.1 : Set E3) ⊆ segment ℝ a d)
    (hea : ∀ e : Section34CompactEdgeIndex K K', a ∈ e.1 →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ a d → e = ea)
    (heb₁ : b ∈ eb.1) (heb₂ : convexHull ℝ (eb.1 : Set E3) ⊆ segment ℝ b c)
    (heb : ∀ e : Section34CompactEdgeIndex K K', b ∈ e.1 →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ b c → e = eb)
    (hec₁ : c ∈ ec.1) (hec₂ : convexHull ℝ (ec.1 : Set E3) ⊆ segment ℝ c a)
    (hec : ∀ e : Section34CompactEdgeIndex K K', c ∈ e.1 →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ c a → e = ec)
    (hed₁ : d ∈ ed.1) (hed₂ : convexHull ℝ (ed.1 : Set E3) ⊆ segment ℝ d b)
    (hed : ∀ e : Section34CompactEdgeIndex K K', d ∈ e.1 →
      convexHull ℝ (e.1 : Set E3) ⊆ segment ℝ d b → e = ed)
    {sacd sabc sbcd sabd : Section34CompactSimplexIndex K 3} (hsacd : sacd.1 = {a, c, d})
    (hsabc : sabc.1 = {a, b, c}) (hsbcd : sbcd.1 = {b, c, d}) (hsabd : sabd.1 = {a, b, d}) :
    ∃ (R A Ω : Set E3), IsPLBall 3 R ∧
      frontier R = A ∪ (tgtD sacd ∪ tgtD sabc ∪ tgtD sbcd ∪ tgtD sabd) ∪ Ω ∧
      A ⊆ frontier (section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d) ∧
      Ω ⊆ frontier (section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b) ∧
      (∃ qA : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn qA (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A ∧
        ∀ k, tgtD (![sacd, sabc, sbcd, sabd] k) ∩
          section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d ⊆
            qA '' stdSimplexBoundary 2) ∧
      (∃ qΩ : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn qΩ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Ω ∧
        ∀ k, tgtD (![sacd, sabc, sbcd, sabd] k) ∩
          section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b ⊆
            qΩ '' stdSimplexBoundary 2) ∧
      Ω ∩ section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d ⊆ A ∧
      A ∩ section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b ⊆ Ω ∧
      Disjoint (interior R)
        (section34CompactClawBall (section34CompactVertexBallImage src f₁) a b c d ∪
          section34CompactClawBall (section34CompactVertexBallImage src f₁) d c a b) := by
  classical
  obtain ⟨hinj, h12, hH₁, hH₂, hHint⟩ := hcut.clawBall_holes hf₁ ht htabcd hab hac had hbc hbd
    hcd hea₁ hea₂ hea heb₁ heb₂ heb hec₁ hec₂ hec hed₁ hed₂ hed
  obtain ⟨pin, pout, γ₁, γ₂, hp, hq, hDi, hDj, hDo, hDb, hint, hg₁, hg₂⟩ :=
    hdisk.exists_faceRuns_of_tetra hcut hf₁ ht htabcd hab hac had hbc hbd hcd hea₁ hea₂ heb₁
      heb₂ hec₁ hec₂ hed₁ hed₂ hinj h12 hsacd hsabc hsbcd hsabd
  set V := section34CompactVertexBallImage src f₁
  set B₁ := section34CompactClawBall V a b c d
  set B₂ := section34CompactClawBall V d c a b
  set eH : Fin 4 → Section34CompactEdgeIndex K K' := ![ec, eb, ed, ea]
  set F : Fin 4 → Section34CompactSimplexIndex K 3 := ![sacd, sabc, sbcd, sabd]
  have ha : a ∈ t := by rw [htabcd]; simp
  have hb : b ∈ t := by rw [htabcd]; simp
  have hc : c ∈ t := by rw [htabcd]; simp
  have hd : d ∈ t := by rw [htabcd]; simp
  have hB₁ : IsPLBall 3 B₁ :=
    hcut.isPLBall_section34CompactClawBall hf₁ ht ha hb hc hd hab hac hbd had hbc hcd
  have hB₂ : IsPLBall 3 B₂ :=
    hcut.isPLBall_section34CompactClawBall hf₁ ht hd hc ha hb hcd.symm had.symm hbc.symm
      hbd.symm hac.symm hab
  have hB₁c : IsClosed B₁ := hB₁.isPolyhedron.isClosed
  obtain ⟨hD1, -, hD3, hD4, hD5, -⟩ := id hdisk
  have hBV : ∀ x y x' y' : E3, section34CompactClawBall V x y x' y' ⊆ ⋃ w, V w :=
    fun _ _ _ _ => iUnion₂_subset fun w _ => subset_iUnion V w
  have hDfr : ∀ (s : Section34CompactSimplexIndex K 3) {B : Set E3}, B ⊆ ⋃ w, V w →
      tgtD s ∩ B ⊆ frontier B := by
    intro s B hB z hz
    have hzDb : z ∈ tgtDBd s := by
      rw [← hD3 s]
      exact ⟨hz.1, hB hz.2⟩
    exact ⟨subset_closure hz.2, fun hzi => (hD4 s hzDb).2 (interior_mono hB hzi)⟩
  have hrHex : ∀ k, ∃ q : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (section34CompactSplitDiskImage src f₁ (eH k)) ∧
        section34CompactSplitDiskImage srcBd f₁ (eH k) = q '' stdSimplexBoundary 2 := fun k =>
    (hcut.isPLCellOn_splitDiskImage hf₁ (eH k)).exists_isPLHomeomorphOn_stdSimplex
  choose rH hrH hrHb using hrHex
  have hqDex : ∀ k, ∃ q : (Fin 3 → ℝ) → E3,
      IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (tgtD (F k)) ∧
        tgtDBd (F k) = q '' stdSimplexBoundary 2 := fun k =>
    (hD1 (F k)).exists_isPLHomeomorphOn_stdSimplex
  choose qD hqD hqDb using hqDex
  have hHdisj : Pairwise fun k l => Disjoint (section34CompactSplitDiskImage src f₁ (eH k))
      (section34CompactSplitDiskImage src f₁ (eH l)) := fun k l hkl =>
    hcut.disjoint_splitDiskImage hf₁ (hinj k l hkl)
  have hHB₁ : ∀ k, section34CompactSplitDiskImage src f₁ (eH k) ⊆ B₁ := fun k =>
    (hH₁ k).trans hB₁c.frontier_subset
  have hne : ∀ {s s' : Section34CompactSimplexIndex K 3} {u : E3}, u ∈ s.1 → u ∉ s'.1 →
      s ≠ s' := fun hu hu' h => hu' (h ▸ hu)
  have hmem : ∀ {s : Finset E3} {x y z u : E3}, s = {x, y, z} → (u = x ∨ u = y ∨ u = z) →
      u ∈ s := by
    intro s x y z u hs hu
    rw [hs]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hu
  have hnmem : ∀ {s : Finset E3} {x y z u : E3}, s = {x, y, z} → u ≠ x → u ≠ y → u ≠ z →
      u ∉ s := by
    intro s x y z u hs hx hy hz hu
    rw [hs] at hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with h | h | h
    · exact hx h
    · exact hy h
    · exact hz h
  have h01 : sacd ≠ sabc := hne (hmem hsabc (Or.inr (Or.inl rfl)) : b ∈ sabc.1)
    (hnmem hsacd hab.symm hbc hbd) |>.symm
  have h02 : sacd ≠ sbcd := hne (hmem hsacd (Or.inl rfl) : a ∈ sacd.1) (hnmem hsbcd hab hac had)
  have h03 : sacd ≠ sabd := hne (hmem hsacd (Or.inr (Or.inl rfl)) : c ∈ sacd.1)
    (hnmem hsabd hac.symm hbc.symm hcd)
  have h12' : sabc ≠ sbcd := hne (hmem hsabc (Or.inl rfl) : a ∈ sabc.1) (hnmem hsbcd hab hac had)
  have h13 : sabc ≠ sabd := hne (hmem hsabc (Or.inr (Or.inr rfl)) : c ∈ sabc.1)
    (hnmem hsabd hac.symm hbc.symm hcd)
  have h23 : sbcd ≠ sabd := hne (hmem hsbcd (Or.inr (Or.inl rfl)) : c ∈ sbcd.1)
    (hnmem hsabd hac.symm hbc.symm hcd)
  have hFinj : ∀ k l : Fin 4, k ≠ l → F k ≠ F l := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    all_goals first
      | exact absurd rfl hkl
      | exact h01 | exact h01.symm | exact h02 | exact h02.symm | exact h03 | exact h03.symm
      | exact h12' | exact h12'.symm | exact h13 | exact h13.symm | exact h23 | exact h23.symm
  have hDdisj : Pairwise fun k l => Disjoint (tgtD (F k)) (tgtD (F l)) := fun k l hkl =>
    hD5 (F k) (F l) (hFinj k l hkl)
  have hsub1 : ∀ k : Fin 4, k + 1 - 1 = k := fun k => add_sub_cancel_right k 1
  obtain ⟨X, Y, qX, qY, β, σ, hqX, hqY, hXY, hXYi, hσ, hβb, hXH, hqXb, hqYb⟩ :=
    exists_split_of_four_runs (H := fun k => section34CompactSplitDiskImage src f₁ (eH k))
      (r := fun k => tgtD (F k) ∩ B₁) hB₁ hrH hH₁ hHdisj (fun k => (hg₁ k).1)
      (fun k => hDfr (F k) (hBV _ _ _ _)) (fun k l hkl => (hDdisj hkl).mono inter_subset_left
        inter_subset_left)
      (fun k => by
        rw [(hg₁ k).2.2, ← hDj k]
        ext z
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hHB₁ k h.2⟩, h.2⟩⟩)
      (fun k => by
        rw [(hg₁ (k + 1)).2.1]
        have h := hDi (k + 1)
        rw [hsub1 k] at h
        rw [← h]
        ext z
        exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hHB₁ k h.2⟩, h.2⟩⟩)
      (fun k l h1 h2 => by
        have hl : l ≠ k - 1 := fun h => h2 (by rw [h, sub_add_cancel])
        exact subset_eq_empty (inter_subset_inter_left _ inter_subset_left) (hDo k l hl h1))
      (fun k => by
        rw [(hg₁ k).2.2, ← hrHb k]
        exact hq k)
      (fun k => by
        rw [(hg₁ (k + 1)).2.1, ← hrHb k]
        have h := hp (k + 1)
        rw [hsub1 k] at h
        exact h)
  obtain ⟨R, A, Ω, qA, qΩ, hR, hRf, hAXY, hqA, hqAb, hqΩ, hqΩb, hΩB₂, hΩB₁, hdisj⟩ :=
    exists_isPLBall_frontier_eq_of_two_balls hB₁ hB₂ hrH hHdisj h12 hH₁ hH₂
      (fun k => by rw [← hrHb k]; exact hHint k) (D := fun k => tgtD (F k))
      (ρ₁ := fun k => tgtD (F k) ∩ B₁) (ρ₂ := fun k => tgtD (F k) ∩ B₂) hqD hDdisj
      (fun k => (hg₁ k).1) (fun k => (hg₂ k).1) (fun _ => rfl) (fun _ => rfl)
      (fun k => by rw [← hqDb k]; exact hDb k)
      (fun k => by rw [(hg₁ k).2.1, (hg₁ k).2.2]; exact hint k)
      (fun k => by rw [(hg₂ k).2.1, (hg₂ k).2.2]; exact hint k)
      (fun k => hDfr (F k) (hBV _ _ _ _)) (fun k => hDfr (F k) (hBV _ _ _ _)) hqX hqY hXY hXYi
      hσ hβb hXH hqXb hqYb
  have hAB₁ : A ⊆ frontier B₁ := by
    rw [← hXY]
    rcases hAXY with rfl | rfl
    · exact subset_union_left.trans subset_union_left
    · exact subset_union_right.trans subset_union_left
  refine ⟨R, A, Ω, hR, ?_, hAB₁, hΩB₂, ⟨qA, hqA, fun k => ?_⟩, ⟨qΩ, hqΩ, fun k => ?_⟩, ?_, ?_,
    hdisj⟩
  · rw [hRf, iUnion_fin_four]
    rfl
  · rw [hqAb]
    exact (subset_iUnion (fun k => tgtD (F k) ∩ B₁) k).trans subset_union_left
  · rw [hqΩb]
    exact (subset_iUnion (fun k => tgtD (F k) ∩ B₂) k).trans subset_union_left
  · rw [hΩB₁]
    exact iUnion_subset fun k => inter_subset_left
  · rintro z ⟨hzA, hz2⟩
    have hz12 : z ∈ B₁ ∩ B₂ := ⟨hB₁c.frontier_subset (hAB₁ hzA), hz2⟩
    rw [h12] at hz12
    obtain ⟨k, hk⟩ := mem_iUnion.mp hz12
    have hzb : z ∈ qΩ '' stdSimplexBoundary 2 := by
      rw [hqΩb]
      exact Or.inr (mem_iUnion.mpr ⟨k, hzA, hk⟩)
    rw [← hqΩ.image_eq]
    exact image_mono (fun x hx => hx.1) hzb

end DifferentialGeometry.Topology.PiecewiseLinear
