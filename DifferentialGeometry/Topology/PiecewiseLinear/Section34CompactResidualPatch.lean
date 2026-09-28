/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualForeign
import DifferentialGeometry.Topology.PiecewiseLinear.CircleArcCycle

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section General

variable {X : Type*} [TopologicalSpace X]

theorem subset_or_disjoint_of_isPreconnected_of_locally_subset {A P : Set X}
    (hA : IsPreconnected A) (hP : IsClosed P)
    (hloc : ∀ y ∈ A, y ∈ P → ∃ U ∈ 𝓝 y, U ∩ A ⊆ P) : A ⊆ P ∨ Disjoint A P := by
  have hsep : ∀ y ∈ A, y ∈ P → y ∉ closure (A \ P) := by
    intro y hyA hyP hycl
    obtain ⟨U, hU, hUA⟩ := hloc y hyA hyP
    obtain ⟨z, hzU, hzA, hzP⟩ := mem_closure_iff_nhds.mp hycl U hU
    exact hzP (hUA ⟨hzU, hzA⟩)
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hA P (closure (A \ P)) hP
    isClosed_closure (fun y hy => by
      by_cases hyP : y ∈ P
      · exact Or.inl hyP
      · exact Or.inr (subset_closure ⟨hy, hyP⟩))
    (eq_empty_iff_forall_notMem.mpr fun y hy => hsep y hy.1 hy.2.1 hy.2.2) with h | h
  · exact Or.inl h
  · exact Or.inr (Set.disjoint_left.mpr fun y hyA hyP => hsep y hyA hyP (h hyA))

theorem mem_frontier_union_of_notMem {A B : Set X} (hB : IsClosed B) {q : X}
    (hq : q ∈ frontier A) (hqB : q ∉ B) : q ∈ frontier (A ∪ B) := by
  refine ⟨closure_mono subset_union_left hq.1, fun hqi => hq.2 ?_⟩
  refine mem_interior.mpr ⟨interior (A ∪ B) ∩ Bᶜ, fun z hz => ?_,
    isOpen_interior.inter hB.isOpen_compl, ⟨hqi, hqB⟩⟩
  rcases interior_subset hz.1 with h | h
  · exact h
  · exact absurd h hz.2

theorem union_closure_sdiff_eq_of_subset {S T : Set X} (hS : IsClosed S) (hT : T ⊆ S) :
    T ∪ closure (S \ T) = S := by
  refine Subset.antisymm (union_subset hT (closure_minimal sdiff_subset hS)) fun z hz => ?_
  by_cases hzT : z ∈ T
  · exact Or.inl hzT
  · exact Or.inr (subset_closure ⟨hz, hzT⟩)

end General

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}
  {fblBd tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set E3}
  {tgtA tgtABd : Section34CompactArcIndex K K' → Set E3}
  {tgtP : Section34CompactMarkIndex K K' → Set E3}

theorem residual_inter_vertexBallImage_subset_frontier {t : Section34CompactSimplexIndex K 4}
    {R : Set E3} (hR : IsPLBall 3 R)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    {w : Section34CompactVertexIndex K K'} (hw : Section34Incident w.1 t.1) :
    R ∩ section34CompactVertexBallImage src f₁ w ⊆
      frontier (section34CompactVertexBallImage src f₁ w) := by
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  rintro z ⟨hzR, hzV⟩
  refine ⟨subset_closure hzV, fun hzi => ?_⟩
  have hzc : z ∈ closure (interior R) := by
    rw [hR.closure_interior_of_finrank hdim]
    exact hzR
  obtain ⟨q, hqV, hqR⟩ := mem_closure_iff.mp hzc _ isOpen_interior hzi
  exact Set.disjoint_left.mp hint hqR (mem_iUnion₂.mpr ⟨w, hw, interior_subset hqV⟩)

theorem Section34CompactCutFrame.residual_inter_splitDiskImage_subset
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {t : Section34CompactSimplexIndex K 4} {R : Set E3} (hR : IsPLBall 3 R)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    (h7 : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
      R ∩ section34CompactVertexBallImage src f₁ w = ∅)
    (e : Section34CompactEdgeIndex K K') :
    R ∩ section34CompactSplitDiskImage src f₁ e ⊆ section34CompactSplitDiskImage srcBd f₁ e := by
  have hdim : Module.finrank ℝ E3 = 2 + 1 := by simp
  intro y hy
  by_contra hyb
  have hyi := hcut.splitDiskImage_sdiff_subset_interior hf₁ e ⟨hy.2, hyb⟩
  have hyc : y ∈ closure (interior R) := by
    rw [hR.closure_interior_of_finrank hdim]
    exact hy.1
  obtain ⟨q, hqV, hqR⟩ := mem_closure_iff.mp hyc _ isOpen_interior hyi
  obtain ⟨u, hqu⟩ := mem_iUnion.mp (interior_subset hqV)
  by_cases hu : Section34Incident u.1 t.1
  · exact Set.disjoint_left.mp hint hqR (mem_iUnion₂.mpr ⟨u, hu, hqu⟩)
  · have h0 : q ∈ R ∩ section34CompactVertexBallImage src f₁ u := ⟨interior_subset hqR, hqu⟩
    rw [h7 u hu] at h0
    exact h0

theorem Section34CompactFaceDiskFamily.exists_faceArc_runs
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34CompactSimplexIndex K 4} {w : Section34CompactVertexIndex K K'} {m : ℕ}
    {sK : Fin (m + 2) → Section34CompactSimplexIndex K 3}
    {eK : Fin (m + 2) → Section34CompactEdgeIndex K K'}
    (hsK : ∀ k, Section34Incident (sK k).1 t.1) (hwsK : ∀ k, Section34Incident w.1 (sK k).1)
    (hweK : ∀ k, w.1 ⊆ (eK k).1) (heinj : Function.Injective eK)
    (hinc : ∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k)
    (hecomp : ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 t.1 → w.1 ⊆ e.1 →
      ∃ k, e = eK k) (k : Fin (m + 2)) :
    ∃ ρ : ℝ → E3, IsPLHomeomorphOn ρ (Icc 0 1) (tgtA ⟨(sK k, w), hwsK k⟩) ∧
      tgtD (sK k) ∩ section34CompactSplitDiskImage src f₁ (eK k) = {ρ 1} ∧
      ∀ l, l + 1 = k → tgtD (sK k) ∩ section34CompactSplitDiskImage src f₁ (eK l) = {ρ 0} := by
  obtain ⟨-, -, -, -, -, hA6, -, -, -, -, -, hA12⟩ := id hdisk
  have hEsub : ∀ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 →
      section34CompactSplitDiskImage src f₁ e ⊆ section34CompactVertexBallImage src f₁ w :=
    fun e he => (hcut.splitDiskImage_subset_frontier hf₁ he).trans
      (hcut.isPLCellOn_vertexBallImage hf₁ w).isCompact.isClosed.frontier_subset
  have hrV : tgtA ⟨(sK k, w), hwsK k⟩ =
      tgtD (sK k) ∩ section34CompactVertexBallImage src f₁ w :=
    (hdisk.faceDisk_inter_vertexBallImage_eq ⟨(sK k, w), hwsK k⟩).symm
  obtain ⟨p, hp, -⟩ := hdisk.exists_faceDisk_inter_splitDiskImage_eq_singleton hcut hf₁ (sK k)
    (eK k) ((hinc k k).mpr (Or.inl rfl))
  obtain ⟨q, hq, -⟩ := hdisk.exists_faceDisk_inter_splitDiskImage_eq_singleton hcut hf₁ (sK k)
    (eK (k - 1)) ((hinc k (k - 1)).mpr (Or.inr (sub_add_cancel k 1)))
  have hpred : ∀ l, l + 1 = k → l = k - 1 := fun l hl => by rw [← hl, add_sub_cancel_right]
  have hpD : p ∈ tgtD (sK k) := (hp.symm.subset (mem_singleton p)).1
  have hpE : p ∈ section34CompactSplitDiskImage src f₁ (eK k) :=
    (hp.symm.subset (mem_singleton p)).2
  have hqD : q ∈ tgtD (sK k) := (hq.symm.subset (mem_singleton q)).1
  have hqE : q ∈ section34CompactSplitDiskImage src f₁ (eK (k - 1)) :=
    (hq.symm.subset (mem_singleton q)).2
  have hne : k - 1 ≠ k := fun h => one_ne_zero (sub_eq_self.mp h)
  have hqp : q ≠ p := fun h => Set.disjoint_left.mp
    (hcut.disjoint_splitDiskImage hf₁ (heinj.ne hne)) hqE (by rw [h]; exact hpE)
  have hbd : tgtABd ⟨(sK k, w), hwsK k⟩ = {q, p} := by
    rw [hA12, hrV]
    apply Subset.antisymm
    · rintro z ⟨⟨hzD, hzV⟩, hzE⟩
      obtain ⟨e, hze⟩ := mem_iUnion.mp hzE
      have hwe := hcut.subset_of_mem_splitDiskImage hf₁ hze hzV
      have hse : Section34Incident e.1 (sK k).1 := by
        by_contra hse
        have h0 : z ∈ tgtD (sK k) ∩ section34CompactSplitDiskImage src f₁ e := ⟨hzD, hze⟩
        rw [hdisk.faceDisk_inter_splitDiskImage_eq_empty hcut hf₁ hse] at h0
        exact h0
      have het : Section34Incident e.1 t.1 := fun x hx =>
        convexHull_min (hsK k) (convex_convexHull ℝ _) (hse hx)
      obtain ⟨l, rfl⟩ := hecomp e het hwe
      rcases (hinc k l).mp hse with hl | hl
      · rw [hl] at hze
        exact Or.inr (hp.subset ⟨hzD, hze⟩)
      · rw [hpred l hl] at hze
        exact Or.inl (hq.subset ⟨hzD, hze⟩)
    · rintro z (hz | hz)
      · rw [hz]
        exact ⟨⟨hqD, hEsub (eK (k - 1)) (hweK (k - 1)) hqE⟩, mem_iUnion.mpr ⟨_, hqE⟩⟩
      · rw [mem_singleton_iff.mp hz]
        exact ⟨⟨hpD, hEsub (eK k) (hweK k) hpE⟩, mem_iUnion.mpr ⟨_, hpE⟩⟩
  obtain ⟨γ, hγ, hγb⟩ := (hA6 ⟨(sK k, w), hwsK k⟩).exists_isPLHomeomorphOn_Icc
  rw [hbd] at hγb
  rcases Set.pair_eq_pair_iff.mp hγb with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact ⟨γ, hγ, by rw [hp, h1], fun l hl => by rw [hpred l hl, hq, h0]⟩
  · obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ → E3, ρ = fun x => γ (1 - x) := ⟨_, rfl⟩
    have hρ : IsPLHomeomorphOn ρ (Icc 0 1) (tgtA ⟨(sK k, w), hwsK k⟩) := by
      rw [hρdef]
      exact isPLHomeomorphOn_comp_one_sub hγ
    have hρ0 : ρ 0 = γ 1 := by
      rw [hρdef]
      norm_num
    have hρ1 : ρ 1 = γ 0 := by
      rw [hρdef]
      norm_num
    exact ⟨ρ, hρ, by rw [hρ1, hp, h1], fun l hl => by rw [hρ0, hpred l hl, hq, h0]⟩

theorem Section34CompactCutFrame.residual_inter_vertexBallImage_eq_of_sides
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34CompactSimplexIndex K 4} {R : Set E3} (hR : IsPLBall 3 R)
    (hfr : frontier R ⊆ (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    (h7 : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
      R ∩ section34CompactVertexBallImage src f₁ w = ∅)
    {w : Section34CompactVertexIndex K K'} (hw : Section34Incident w.1 t.1) {m : ℕ}
    {sK : Fin (m + 2) → Section34CompactSimplexIndex K 3}
    {eK : Fin (m + 2) → Section34CompactEdgeIndex K K'}
    (hwsK : ∀ k, Section34Incident w.1 (sK k).1) (hweK : ∀ k, w.1 ⊆ (eK k).1)
    (heKt : ∀ k, Section34Incident (eK k).1 t.1)
    (hscomp : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      Section34Incident w.1 s.1 → ∃ k, s = sK k)
    {A B : Set E3} {qA qB : (Fin 3 → ℝ) → E3}
    (hqA : IsPLHomeomorphOn qA (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A)
    (hqB : IsPLHomeomorphOn qB (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) B)
    (hAB : A ∪ B ∪ (⋃ k, section34CompactSplitDiskImage src f₁ (eK k)) =
      frontier (section34CompactVertexBallImage src f₁ w))
    (hABi : A ∩ B = ⋃ k, tgtA ⟨(sK k, w), hwsK k⟩)
    (hH : ∀ k, A ∩ section34CompactSplitDiskImage src f₁ (eK k) ∪
      B ∩ section34CompactSplitDiskImage src f₁ (eK k) =
        section34CompactSplitDiskImage srcBd f₁ (eK k))
    (hqBb : qB '' stdSimplexBoundary 2 = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
      ⋃ k, B ∩ section34CompactSplitDiskImage src f₁ (eK k))
    (hAR : A \ qA '' stdSimplexBoundary 2 ⊆ R)
    (hBR : Disjoint (B \ qB '' stdSimplexBoundary 2) R) :
    R ∩ section34CompactVertexBallImage src f₁ w = A ∧
      ∀ k, R ∩ section34CompactSplitDiskImage src f₁ (eK k) =
        A ∩ section34CompactSplitDiskImage src f₁ (eK k) := by
  have hRc : IsClosed R := hR.isPolyhedron.isClosed
  have hVball : ∀ u, IsPLBall 3 (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isPLBall_three
  have hVc : ∀ u, IsClosed (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hVball u).isPolyhedron.isClosed
  obtain ⟨hD1, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hAR' : A ⊆ R := fun z hz => closure_minimal hAR hRc
    ((hqA.closure_sdiff_image_stdSimplexBoundary (n := 1)).symm.subset hz)
  have hAS : A ⊆ frontier (section34CompactVertexBallImage src f₁ w) := fun z hz =>
    hAB.subset (Or.inl (Or.inl hz))
  have hBS : B ⊆ frontier (section34CompactVertexBallImage src f₁ w) := fun z hz =>
    hAB.subset (Or.inl (Or.inr hz))
  have hArun : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ ⊆ A := fun k z hz =>
    (hABi.symm.subset (mem_iUnion.mpr ⟨k, hz⟩)).1
  have hBEA : ∀ k, ∀ y ∈ R, y ∈ B ∩ section34CompactSplitDiskImage src f₁ (eK k) → y ∈ A := by
    intro k y hyR hyBE
    by_contra hyA
    obtain ⟨a, b, hab, habe, -⟩ := hcut.splitDiskImage_eq_inter hf₁ (eK k)
    have hae : a.1 ⊆ (eK k).1 := by
      have h : (a.1 : Set E3) ⊆ (eK k).1 := by
        rw [habe]
        exact subset_union_left
      exact Finset.coe_subset.mp h
    have hbe : b.1 ⊆ (eK k).1 := by
      have h : (b.1 : Set E3) ⊆ (eK k).1 := by
        rw [habe]
        exact subset_union_right
      exact Finset.coe_subset.mp h
    obtain ⟨w', hww', hw'e⟩ : ∃ w' : Section34CompactVertexIndex K K', w ≠ w' ∧
        w'.1 ⊆ (eK k).1 := by
      rcases eq_or_eq_of_section34CompactVertexIndex_subset (eK k) habe (hweK k) with h | h
      · exact ⟨b, by rw [h]; exact hab, hbe⟩
      · exact ⟨a, by rw [h]; exact hab.symm, hae⟩
    have hw't : Section34Incident w'.1 t.1 := fun z hz => heKt k (hw'e hz)
    have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww' (hweK k) hw'e
    obtain ⟨qE, hqE, -⟩ :=
      (hcut.isPLCellOn_splitDiskImage hf₁ (eK k)).exists_isPLHomeomorphOn_stdSimplex
    have hW := isPLBall_union_of_inter_eq_of_subset_frontier (hVball w) (hVball w') ⟨qE, hqE⟩
      hinter (hcut.splitDiskImage_subset_frontier hf₁ hw'e)
    have hyEb := hcut.residual_inter_splitDiskImage_subset hf₁ hR hint h7 (eK k) ⟨hyR, hyBE.2⟩
    have hyW : y ∈ frontier (section34CompactVertexBallImage src f₁ w ∪
        section34CompactVertexBallImage src f₁ w') :=
      boundary_subset_frontier_union_of_inter_eq (hVball w) (hVball w')
        (hcut.isPLCellOn_splitDiskImage hf₁ (eK k)) hinter
        (hcut.splitDiskImage_subset_frontier hf₁ (hweK k)) hyEb
    have hyww' : y ∈ section34CompactVertexBallImage src f₁ w ∩
        section34CompactVertexBallImage src f₁ w' := by
      rw [hinter]
      exact hyBE.2
    obtain ⟨U, hU, hUR, -⟩ := hcut.exists_mem_nhds_frontier_subset_residual hf₁ hR hfr hint hDc
      hW (union_subset (subset_iUnion₂_of_subset w hw subset_rfl)
        (subset_iUnion₂_of_subset w' hw't subset_rfl)) hyR hyW
      (fun u _ hyu => by
        by_cases huw : u = w
        · rw [huw]
          exact subset_union_left
        · by_cases huw' : u = w'
          · rw [huw']
            exact subset_union_right
          · have h0 : y ∈ section34CompactVertexBallImage src f₁ u ∩
                section34CompactVertexBallImage src f₁ w ∩
                section34CompactVertexBallImage src f₁ w' := ⟨⟨hyu, hyww'.1⟩, hyww'.2⟩
            rw [hcut.vertexBallImage_inter_inter_eq_empty hf₁ huw huw' hww'] at h0
            exact h0.elim)
      (fun s hs hys => by
        have hse : Section34Incident (eK k).1 s.1 := by
          by_contra hse
          have h0 : y ∈ tgtD s ∩ section34CompactSplitDiskImage src f₁ (eK k) := ⟨hys, hyBE.2⟩
          rw [hdisk.faceDisk_inter_splitDiskImage_eq_empty hcut hf₁ hse] at h0
          exact h0
        have hws : Section34Incident w.1 s.1 := fun z hz => hse (hweK k hz)
        obtain ⟨j, rfl⟩ := hscomp s hs hws
        exact hyA (hArun j ((hdisk.faceDisk_inter_vertexBallImage_eq ⟨(sK j, w), hwsK j⟩).subset
          ⟨hys, hyww'.1⟩)))
    have hyB : y ∈ closure (B \ qB '' stdSimplexBoundary 2) := by
      rw [hqB.closure_sdiff_image_stdSimplexBoundary (n := 1)]
      exact hyBE.1
    obtain ⟨q, hqU, hqB'⟩ := mem_closure_iff_nhds.mp hyB U hU
    have hqS : q ∈ frontier (section34CompactVertexBallImage src f₁ w) := hBS hqB'.1
    have hqw' : q ∉ section34CompactVertexBallImage src f₁ w' := fun hq => hqB'.2 (by
      rw [hqBb]
      refine Or.inr (mem_iUnion.mpr ⟨k, hqB'.1, ?_⟩)
      rw [← hinter]
      exact ⟨(hVc w).frontier_subset hqS, hq⟩)
    exact Set.disjoint_left.mp hBR hqB'
      (hUR ⟨hqU, mem_frontier_union_of_notMem (hVc w') hqS hqw'⟩)
  have hRE : ∀ k, R ∩ section34CompactSplitDiskImage src f₁ (eK k) =
      A ∩ section34CompactSplitDiskImage src f₁ (eK k) := by
    intro k
    apply Subset.antisymm
    · intro y hy
      have hyEb := hcut.residual_inter_splitDiskImage_subset hf₁ hR hint h7 (eK k) hy
      rw [← hH k] at hyEb
      rcases hyEb with hyA | hyB
      · exact hyA
      · exact ⟨hBEA k y hy.1 hyB, hy.2⟩
    · exact fun y hy => ⟨hAR' hy.1, hy.2⟩
  refine ⟨Subset.antisymm ?_ fun y hy => ⟨hAR' hy, (hVc w).frontier_subset (hAS hy)⟩, hRE⟩
  intro y hy
  have hyS := residual_inter_vertexBallImage_subset_frontier hR hint hw hy
  rw [← hAB] at hyS
  rcases hyS with (hyA | hyB) | hyE
  · exact hyA
  · by_cases hyb : y ∈ qB '' stdSimplexBoundary 2
    · rw [hqBb] at hyb
      rcases hyb with hyr | hyBE
      · rw [← hABi] at hyr
        exact hyr.1
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hyBE
        exact hBEA k y hy.1 hk
    · exact absurd hy.1 (Set.disjoint_left.mp hBR ⟨hyB, hyb⟩)
  · obtain ⟨k, hk⟩ := mem_iUnion.mp hyE
    have h0 : y ∈ R ∩ section34CompactSplitDiskImage src f₁ (eK k) := ⟨hy.1, hk⟩
    rw [hRE k] at h0
    exact h0.1

theorem Section34CompactCutFrame.residual_sides
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34CompactSimplexIndex K 4} {R : Set E3} (hR : IsPLBall 3 R)
    (hDR : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ frontier R)
    (hfr : frontier R ⊆ (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    (hio : ∀ a : Section34CompactArcIndex K K', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ R)
    (h7 : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
      R ∩ section34CompactVertexBallImage src f₁ w = ∅)
    {w : Section34CompactVertexIndex K K'} {m : ℕ}
    {sK : Fin (m + 2) → Section34CompactSimplexIndex K 3}
    {eK : Fin (m + 2) → Section34CompactEdgeIndex K K'}
    (hsK : ∀ k, Section34Incident (sK k).1 t.1) (hwsK : ∀ k, Section34Incident w.1 (sK k).1)
    (hsinj : Function.Injective sK)
    (hscomp : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      Section34Incident w.1 s.1 → ∃ k, s = sK k)
    (hecomp : ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 t.1 → w.1 ⊆ e.1 →
      ∃ k, e = eK k)
    {X Y : Set E3} {qX qY : (Fin 3 → ℝ) → E3}
    (hqX : IsPLHomeomorphOn qX (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) X)
    (hqY : IsPLHomeomorphOn qY (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Y)
    (hXY : X ∪ Y ∪ (⋃ k, section34CompactSplitDiskImage src f₁ (eK k)) =
      frontier (section34CompactVertexBallImage src f₁ w))
    (hqXb : qX '' stdSimplexBoundary 2 = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
      ⋃ k, X ∩ section34CompactSplitDiskImage src f₁ (eK k))
    (hqYb : qY '' stdSimplexBoundary 2 = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
      ⋃ k, Y ∩ section34CompactSplitDiskImage src f₁ (eK k)) :
    (X \ qX '' stdSimplexBoundary 2 ⊆ R ∧ Disjoint (Y \ qY '' stdSimplexBoundary 2) R) ∨
      (Y \ qY '' stdSimplexBoundary 2 ⊆ R ∧ Disjoint (X \ qX '' stdSimplexBoundary 2) R) := by
  have hw : Section34Incident w.1 t.1 := fun z hz =>
    convexHull_min (hsK 0) (convex_convexHull ℝ _) (hwsK 0 hz)
  have hRc : IsClosed R := hR.isPolyhedron.isClosed
  have hVc : ∀ u, IsClosed (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isCompact.isClosed
  have hEc : ∀ e, IsClosed (section34CompactSplitDiskImage src f₁ e) := fun e =>
    (hcut.isPLCellOn_splitDiskImage hf₁ e).isCompact.isClosed
  obtain ⟨hD1, -, -, -, hD5, hA6, -, hD8, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hAc : ∀ a, IsClosed (tgtA a) := fun a => (hA6 a).isCompact.isClosed
  have hrD : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ ⊆ tgtD (sK k) := fun k z hz =>
    ((hdisk.faceDisk_inter_vertexBallImage_eq ⟨(sK k, w), hwsK k⟩).symm.subset hz).1
  have hgen : ∀ (Z : Set E3) (qZ : (Fin 3 → ℝ) → E3),
      Z ⊆ frontier (section34CompactVertexBallImage src f₁ w) →
      qZ '' stdSimplexBoundary 2 = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
        ⋃ k, Z ∩ section34CompactSplitDiskImage src f₁ (eK k) →
      ∀ y ∈ Z \ qZ '' stdSimplexBoundary 2, y ∈ R →
        ∃ U ∈ 𝓝 y, U ∩ (Z \ qZ '' stdSimplexBoundary 2) ⊆ R := by
    intro Z qZ hZS hqZb y hy hyR
    have hyS := hZS hy.1
    have hyV := (hVc w).frontier_subset hyS
    obtain ⟨U, hU, hUR, -⟩ := hcut.exists_mem_nhds_frontier_subset_residual hf₁ hR hfr hint hDc
      ((hcut.isPLCellOn_vertexBallImage hf₁ w).isPLBall_three)
      (subset_iUnion₂_of_subset w hw subset_rfl) hyR hyS
      (fun u _ hyu => by
        by_cases huw : u = w
        · exact (congrArg (section34CompactVertexBallImage src f₁) huw).subset
        · exfalso
          obtain ⟨e, hye⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ huw hyu hyV
          have hwe := hcut.subset_of_mem_splitDiskImage hf₁ hye hyV
          by_cases het : Section34Incident e.1 t.1
          · obtain ⟨l, rfl⟩ := hecomp e het hwe
            exact hy.2 (by
              rw [hqZb]
              exact Or.inr (mem_iUnion.mpr ⟨l, hy.1, hye⟩))
          · have h0 : y ∈ R ∩ section34CompactSplitDiskImage src f₁ e := ⟨hyR, hye⟩
            rw [hcut.residual_inter_splitDiskImage_eq_empty hf₁ h7 het] at h0
            exact h0)
      (fun s hs hys => by
        have hws : Section34Incident w.1 s.1 := by
          by_contra hws
          have h0 : y ∈ tgtD s ∩ section34CompactVertexBallImage src f₁ w := ⟨hys, hyV⟩
          rw [hD8 s w hws] at h0
          exact h0
        obtain ⟨j, rfl⟩ := hscomp s hs hws
        exact hy.2 (by
          rw [hqZb]
          exact Or.inl (mem_iUnion.mpr ⟨j, (hdisk.faceDisk_inter_vertexBallImage_eq
            ⟨(sK j, w), hwsK j⟩).subset ⟨hys, hyV⟩⟩)))
    exact ⟨U, hU, fun z hz => hUR ⟨hz.1, hZS hz.2.1⟩⟩
  have hXS : X ⊆ frontier (section34CompactVertexBallImage src f₁ w) := fun z hz =>
    hXY.subset (Or.inl (Or.inl hz))
  have hYS : Y ⊆ frontier (section34CompactVertexBallImage src f₁ w) := fun z hz =>
    hXY.subset (Or.inl (Or.inr hz))
  have hXo : X \ qX '' stdSimplexBoundary 2 ⊆ R ∨
      Disjoint (X \ qX '' stdSimplexBoundary 2) R :=
    subset_or_disjoint_of_isPreconnected_of_locally_subset
      (hqX.isConnected_sdiff_image_stdSimplexBoundary (n := 1)).isPreconnected hRc
      (hgen X qX hXS hqXb)
  have hYo : Y \ qY '' stdSimplexBoundary 2 ⊆ R ∨
      Disjoint (Y \ qY '' stdSimplexBoundary 2) R :=
    subset_or_disjoint_of_isPreconnected_of_locally_subset
      (hqY.isConnected_sdiff_image_stdSimplexBoundary (n := 1)).isPreconnected hRc
      (hgen Y qY hYS hqYb)
  obtain ⟨y₀, hy₀A, hy₀E⟩ := hdisk.exists_mem_faceArc_notMem_splitDiskImage ⟨(sK 0, w), hwsK 0⟩
  have hFc : IsClosed ((⋃ k, section34CompactSplitDiskImage src f₁ (eK k)) ∪
      ⋃ (k : Fin (m + 2)) (_ : k ≠ 0), tgtA ⟨(sK k, w), hwsK k⟩) :=
    (isClosed_iUnion_of_finite fun k => hEc (eK k)).union
      (isClosed_iUnion_of_finite fun k => isClosed_iUnion_of_finite fun _ => hAc _)
  have hy₀F : y₀ ∉ (⋃ k, section34CompactSplitDiskImage src f₁ (eK k)) ∪
      ⋃ (k : Fin (m + 2)) (_ : k ≠ 0), tgtA ⟨(sK k, w), hwsK k⟩ := by
    rintro (hy | hy)
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hy
      exact hy₀E (eK k) hk
    · obtain ⟨k, hk0, hk⟩ := mem_iUnion₂.mp hy
      exact Set.disjoint_left.mp (hD5 (sK 0) (sK k) (hsinj.ne (Ne.symm hk0))) (hrD 0 hy₀A)
        (hrD k hk)
  obtain ⟨⟨z, hzU, hzS, hzR, hzD⟩, z', hz'U, hz'S, hz'R⟩ :=
    hio ⟨(sK 0, w), hwsK 0⟩ (hsK 0) y₀ hy₀A hy₀E _ (hFc.isOpen_compl.mem_nhds hy₀F)
  have hclass : ∀ x ∈ ((⋃ k, section34CompactSplitDiskImage src f₁ (eK k)) ∪
      ⋃ (k : Fin (m + 2)) (_ : k ≠ 0), tgtA ⟨(sK k, w), hwsK k⟩)ᶜ,
      x ∈ frontier (section34CompactVertexBallImage src f₁ w) → x ∉ tgtD (sK 0) →
      x ∈ X \ qX '' stdSimplexBoundary 2 ∨ x ∈ Y \ qY '' stdSimplexBoundary 2 := by
    intro x hxF hxS hxD
    have hxE : ∀ k, x ∉ section34CompactSplitDiskImage src f₁ (eK k) := fun k hk =>
      hxF (Or.inl (mem_iUnion.mpr ⟨k, hk⟩))
    have hxr : ∀ k, x ∉ tgtA ⟨(sK k, w), hwsK k⟩ := fun k hk => by
      by_cases hk0 : k = 0
      · subst hk0
        exact hxD (hrD 0 hk)
      · exact hxF (Or.inr (mem_iUnion₂.mpr ⟨k, hk0, hk⟩))
    rw [← hXY] at hxS
    rcases hxS with (hxX | hxY) | hxE'
    · refine Or.inl ⟨hxX, fun hb => ?_⟩
      rw [hqXb] at hb
      rcases hb with hb | hb
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hb
        exact hxr k hk
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hb
        exact hxE k hk.2
    · refine Or.inr ⟨hxY, fun hb => ?_⟩
      rw [hqYb] at hb
      rcases hb with hb | hb
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hb
        exact hxr k hk
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hb
        exact hxE k hk.2
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hxE'
      exact absurd hk (hxE k)
  have hz'D : z' ∉ tgtD (sK 0) := fun h =>
    hz'R (hRc.frontier_subset (hDR (sK 0) (hsK 0) h))
  rcases hclass z hzU hzS hzD with hzX | hzY
  · rcases hXo with hXR | hXR
    · rcases hclass z' hz'U hz'S hz'D with hz'X | hz'Y
      · exact absurd (hXR hz'X) hz'R
      · rcases hYo with hYR | hYR
        · exact absurd (hYR hz'Y) hz'R
        · exact Or.inl ⟨hXR, hYR⟩
    · exact absurd hzR (Set.disjoint_left.mp hXR hzX)
  · rcases hYo with hYR | hYR
    · rcases hclass z' hz'U hz'S hz'D with hz'X | hz'Y
      · rcases hXo with hXR | hXR
        · exact absurd (hXR hz'X) hz'R
        · exact Or.inr ⟨hYR, hXR⟩
      · exact absurd (hYR hz'Y) hz'R
    · exact absurd hzR (Set.disjoint_left.mp hYR hzY)

theorem Section34CompactCutFrame.exists_residualPatch
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34CompactSimplexIndex K 4} {R : Set E3} (hR : IsPLBall 3 R)
    (hDR : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ frontier R)
    (hfr : frontier R ⊆ (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34CompactVertexIndex K K')
      (_ : Section34Incident w.1 t.1), section34CompactVertexBallImage src f₁ w))
    (hio : ∀ a : Section34CompactArcIndex K K', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ R)
    (h7 : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
      R ∩ section34CompactVertexBallImage src f₁ w = ∅)
    {w : Section34CompactVertexIndex K K'} {m : ℕ}
    {sK : Fin (m + 2) → Section34CompactSimplexIndex K 3}
    {eK : Fin (m + 2) → Section34CompactEdgeIndex K K'}
    (hsK : ∀ k, Section34Incident (sK k).1 t.1) (hwsK : ∀ k, Section34Incident w.1 (sK k).1)
    (hweK : ∀ k, w.1 ⊆ (eK k).1) (hsinj : Function.Injective sK)
    (heinj : Function.Injective eK)
    (hinc : ∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k)
    (hscomp : ∀ s : Section34CompactSimplexIndex K 3, Section34Incident s.1 t.1 →
      Section34Incident w.1 s.1 → ∃ k, s = sK k)
    (hecomp : ∀ e : Section34CompactEdgeIndex K K', Section34Incident e.1 t.1 → w.1 ⊆ e.1 →
      ∃ k, e = eK k) :
    (∃ q : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (R ∩ section34CompactVertexBallImage src f₁ w) ∧
      q '' stdSimplexBoundary 2 = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
        ⋃ k, R ∩ section34CompactSplitDiskImage src f₁ (eK k)) ∧
    ∀ k, ∃ γ : ℝ → E3,
      IsPLHomeomorphOn γ (Icc 0 1) (R ∩ section34CompactSplitDiskImage src f₁ (eK k)) ∧
      tgtD (sK k) ∩ section34CompactSplitDiskImage src f₁ (eK k) = {γ 0} ∧
      tgtD (sK (k + 1)) ∩ section34CompactSplitDiskImage src f₁ (eK k) = {γ 1} := by
  have hw : Section34Incident w.1 t.1 := fun z hz =>
    convexHull_min (hsK 0) (convex_convexHull ℝ _) (hwsK 0 hz)
  have heKt : ∀ k, Section34Incident (eK k).1 t.1 := fun k z hz =>
    convexHull_min (hsK k) (convex_convexHull ℝ _) (((hinc k k).mpr (Or.inl rfl)) hz)
  have hVball : ∀ u, IsPLBall 3 (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isPLBall_three
  have hVc : ∀ u, IsClosed (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hVball u).isPolyhedron.isClosed
  obtain ⟨-, -, -, hD4, hD5, -, hA7, -⟩ := id hdisk
  have hEsub : ∀ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 →
      section34CompactSplitDiskImage src f₁ e ⊆ section34CompactVertexBallImage src f₁ w :=
    fun e he => (hcut.splitDiskImage_subset_frontier hf₁ he).trans (hVc w).frontier_subset
  have hrV : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ =
      tgtD (sK k) ∩ section34CompactVertexBallImage src f₁ w := fun k =>
    (hdisk.faceDisk_inter_vertexBallImage_eq ⟨(sK k, w), hwsK k⟩).symm
  have hrD : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ ⊆ tgtD (sK k) := fun k z hz => ((hrV k).subset hz).1
  choose ρ hρ hρ1 hρ0 using
    hdisk.exists_faceArc_runs hcut hf₁ hsK hwsK hweK heinj hinc hecomp
  choose rH hrH hrHb using fun k =>
    (hcut.isPLCellOn_splitDiskImage hf₁ (eK k)).exists_isPLHomeomorphOn_stdSimplex
  have hmarkb : ∀ k l, ∀ x, tgtD (sK k) ∩ section34CompactSplitDiskImage src f₁ (eK l) = {x} →
      x ∈ rH l '' stdSimplexBoundary 2 := by
    intro k l x hx
    have h := hdisk.faceDisk_inter_splitDiskImage_subset hcut hf₁ (sK k) (eK l)
      (hx.symm.subset (mem_singleton x))
    rw [← hrHb l]
    exact h.2
  have hrB : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ ⊆
      frontier (section34CompactVertexBallImage src f₁ w) := by
    intro k z hz
    have hz' : z ∈ tgtDBd (sK k) ∩ section34CompactVertexBallImage src f₁ w :=
      (hA7 ⟨(sK k, w), hwsK k⟩).symm.subset hz
    exact ⟨subset_closure hz'.2, fun hzi =>
      (hD4 (sK k) hz'.1).2 (interior_mono (subset_iUnion _ w) hzi)⟩
  have hout : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ ∩ section34CompactSplitDiskImage src f₁ (eK k) =
      {ρ k 1} := fun k => by
    rw [hrV k, inter_assoc, inter_eq_right.mpr (hEsub _ (hweK k)), hρ1 k]
  have hin : ∀ k, tgtA ⟨(sK (k + 1), w), hwsK (k + 1)⟩ ∩
      section34CompactSplitDiskImage src f₁ (eK k) = {ρ (k + 1) 0} := fun k => by
    rw [hrV (k + 1), inter_assoc, inter_eq_right.mpr (hEsub _ (hweK k)), hρ0 (k + 1) k rfl]
  have hfar : ∀ k l, l ≠ k → l + 1 ≠ k →
      tgtA ⟨(sK k, w), hwsK k⟩ ∩ section34CompactSplitDiskImage src f₁ (eK l) = ∅ :=
    fun k l hlk hlk' => by
      rw [hrV k, inter_assoc, inter_eq_right.mpr (hEsub _ (hweK l)),
        hdisk.faceDisk_inter_splitDiskImage_eq_empty hcut hf₁
          (fun h => ((hinc k l).mp h).elim hlk hlk')]
  obtain ⟨X, Y, qX, qY, β, σ, τ, hqX, hqY, hXY, hXYi, hσ, hτ, hβb, hXH, hqXb, hqYb⟩ :=
    exists_split_of_runs (hVball w) (H := fun k => section34CompactSplitDiskImage src f₁ (eK k))
      (r := fun k => tgtA ⟨(sK k, w), hwsK k⟩) hrH
      (fun k => hcut.splitDiskImage_subset_frontier hf₁ (hweK k))
      (fun k l hkl => hcut.disjoint_splitDiskImage hf₁ (heinj.ne hkl)) hρ hrB
      (fun k l hkl => (hD5 _ _ (hsinj.ne hkl)).mono (hrD k) (hrD l)) hout hin hfar
      (fun k => hmarkb k k _ (hρ1 k)) (fun k => hmarkb (k + 1) k _ (hρ0 (k + 1) k rfl))
  have hXY' : X ∪ Y ∪ (⋃ k, section34CompactSplitDiskImage src f₁ (eK k)) =
      frontier (section34CompactVertexBallImage src f₁ w) := hXY
  have hXYi' : X ∩ Y = ⋃ k, tgtA ⟨(sK k, w), hwsK k⟩ := hXYi
  have hXH' : ∀ k, (X ∩ section34CompactSplitDiskImage src f₁ (eK k) = β k ∧
      Y ∩ section34CompactSplitDiskImage src f₁ (eK k) =
        closure (rH k '' stdSimplexBoundary 2 \ β k)) ∨
      (X ∩ section34CompactSplitDiskImage src f₁ (eK k) =
        closure (rH k '' stdSimplexBoundary 2 \ β k) ∧
        Y ∩ section34CompactSplitDiskImage src f₁ (eK k) = β k) := hXH
  have hqXb' : qX '' stdSimplexBoundary 2 = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
      ⋃ k, X ∩ section34CompactSplitDiskImage src f₁ (eK k) := hqXb
  have hqYb' : qY '' stdSimplexBoundary 2 = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
      ⋃ k, Y ∩ section34CompactSplitDiskImage src f₁ (eK k) := hqYb
  have hHk : ∀ k, X ∩ section34CompactSplitDiskImage src f₁ (eK k) ∪
      Y ∩ section34CompactSplitDiskImage src f₁ (eK k) =
        section34CompactSplitDiskImage srcBd f₁ (eK k) := fun k => by
    have hcl : IsClosed (rH k '' stdSimplexBoundary 2) :=
      ((hrH k).isPLSphere_image_stdSimplexBoundary (n := 1)).isPolyhedron.isClosed
    rw [hrHb k]
    rcases hXH' k with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact union_closure_sdiff_eq_of_subset hcl (hβb k)
    · rw [h1, h2, union_comm]
      exact union_closure_sdiff_eq_of_subset hcl (hβb k)
  have hkey : ∃ (A : Set E3) (qA : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn qA (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) A ∧
      qA '' stdSimplexBoundary 2 = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
        ⋃ k, A ∩ section34CompactSplitDiskImage src f₁ (eK k) ∧
      R ∩ section34CompactVertexBallImage src f₁ w = A ∧
      (∀ k, R ∩ section34CompactSplitDiskImage src f₁ (eK k) =
        A ∩ section34CompactSplitDiskImage src f₁ (eK k)) ∧
      ∀ k, A ∩ section34CompactSplitDiskImage src f₁ (eK k) = β k ∨
        A ∩ section34CompactSplitDiskImage src f₁ (eK k) =
          closure (rH k '' stdSimplexBoundary 2 \ β k) := by
    rcases hcut.residual_sides hf₁ hdisk hR hDR hfr hint hio h7 hsK hwsK hsinj hscomp hecomp
      hqX hqY hXY' hqXb' hqYb' with ⟨hXR, hYR⟩ | ⟨hYR, hXR⟩
    · obtain ⟨hRV, hRE⟩ := hcut.residual_inter_vertexBallImage_eq_of_sides hf₁ hdisk hR hfr
        hint h7 hw hwsK hweK heKt hscomp hqX hqY hXY' hXYi' hHk hqYb' hXR hYR
      refine ⟨X, qX, hqX, hqXb', hRV, hRE, fun k => ?_⟩
      rcases hXH' k with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact Or.inl h1
      · exact Or.inr h1
    · have hYX : Y ∪ X ∪ (⋃ k, section34CompactSplitDiskImage src f₁ (eK k)) =
          frontier (section34CompactVertexBallImage src f₁ w) := by
        rw [union_comm Y X]
        exact hXY'
      have hYXi : Y ∩ X = ⋃ k, tgtA ⟨(sK k, w), hwsK k⟩ := by
        rw [inter_comm]
        exact hXYi'
      have hHk' : ∀ k, Y ∩ section34CompactSplitDiskImage src f₁ (eK k) ∪
          X ∩ section34CompactSplitDiskImage src f₁ (eK k) =
            section34CompactSplitDiskImage srcBd f₁ (eK k) := fun k => by
        rw [union_comm]
        exact hHk k
      obtain ⟨hRV, hRE⟩ := hcut.residual_inter_vertexBallImage_eq_of_sides hf₁ hdisk hR hfr
        hint h7 hw hwsK hweK heKt hscomp hqY hqX hYX hYXi hHk' hqXb' hYR hXR
      refine ⟨Y, qY, hqY, hqYb', hRV, hRE, fun k => ?_⟩
      rcases hXH' k with ⟨-, h2⟩ | ⟨-, h2⟩
      · exact Or.inr h2
      · exact Or.inl h2
  obtain ⟨A, qA, hqA, hqAb, hRV, hRE, hAE⟩ := hkey
  refine ⟨⟨qA, by rw [hRV]; exact hqA, ?_⟩, fun k => ?_⟩
  · rw [hqAb]
    congr 1
    exact iUnion_congr fun k => (hRE k).symm
  · have harc : ∃ γ : ℝ → E3,
        IsPLHomeomorphOn γ (Icc 0 1) (A ∩ section34CompactSplitDiskImage src f₁ (eK k)) ∧
        γ 0 = ρ k 1 ∧ γ 1 = ρ (k + 1) 0 := by
      rcases hAE k with h | h
      · rw [h]
        exact ⟨σ k, hσ k⟩
      · rw [h]
        exact ⟨τ k, hτ k⟩
    obtain ⟨γ, hγ, hγ0, hγ1⟩ := harc
    refine ⟨γ, by rw [hRE k]; exact hγ, by rw [hγ0]; exact hρ1 k, ?_⟩
    rw [hγ1]
    exact hρ0 (k + 1) k rfl

end DifferentialGeometry.Topology.PiecewiseLinear
