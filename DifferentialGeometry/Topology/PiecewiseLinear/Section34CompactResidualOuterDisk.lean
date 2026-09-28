/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterEnumeration

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}
  {fblBd tgtD tgtDBd : Section34CompactSimplexIndex K 3 → Set E3}
  {tgtA tgtABd : Section34CompactArcIndex K K' → Set E3}
  {tgtP : Section34CompactMarkIndex K K' → Set E3}

theorem Section34CompactFaceDiskFamily.exists_faceArc_runs_of_edges
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {w : Section34CompactVertexIndex K K'} {m : ℕ}
    {sK : Fin (m + 2) → Section34CompactSimplexIndex K 3}
    {eK : Fin (m + 2) → Section34CompactEdgeIndex K K'}
    (hwsK : ∀ k, Section34Incident w.1 (sK k).1)
    (hweK : ∀ k, w.1 ⊆ (eK k).1) (heinj : Function.Injective eK)
    (hinc : ∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k)
    (hedge : ∀ (k : Fin (m + 2)) (e : Section34CompactEdgeIndex K K'), w.1 ⊆ e.1 →
      Section34Incident e.1 (sK k).1 → ∃ l, e = eK l) (k : Fin (m + 2)) :
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
      obtain ⟨l, rfl⟩ := hedge k e hwe hse
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

theorem Section34CompactCutFrame.isPLSphere_outerCircle
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {Rf : Section34CompactSimplexIndex K 4 → Set E3} (hR : ∀ t, IsPLBall 3 (Rf t))
    (hDR : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      Section34Incident s.1 t.1 → tgtD s ⊆ frontier (Rf t))
    (hfr : ∀ t : Section34CompactSimplexIndex K 4, frontier (Rf t) ⊆
      (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : ∀ t : Section34CompactSimplexIndex K 4, Disjoint (interior (Rf t))
      (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w))
    (hio : ∀ (t : Section34CompactSimplexIndex K 4) (a : Section34CompactArcIndex K K'),
      Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ Rf t ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ Rf t)
    (h7 : ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34CompactVertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    {w : Section34CompactVertexIndex K K'} {m : ℕ}
    {sK : Fin (m + 2) → Section34CompactSimplexIndex K 3}
    {eK : Fin (m + 2) → Section34CompactEdgeIndex K K'}
    (hsb : ∀ k, convexHull ℝ ((sK k).1 : Set E3) ⊆ frontier K.space)
    (hwsK : ∀ k, Section34Incident w.1 (sK k).1) (hweK : ∀ k, w.1 ⊆ (eK k).1)
    (hsinj : Function.Injective sK) (heinj : Function.Injective eK)
    (hinc : ∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k)
    (hscomp : ∀ s : Section34CompactSimplexIndex K 3,
      convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space → Section34Incident w.1 s.1 →
        ∃ k, s = sK k)
    (hecomp : ∀ e : Section34CompactEdgeIndex K K',
      convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space → w.1 ⊆ e.1 → ∃ k, e = eK k) :
    IsPLSphere 1 ((⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
      ⋃ k, closure (section34CompactSplitDiskImage srcBd f₁ (eK k) \
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident (eK k).1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ (eK k))) := by
  obtain ⟨-, -, -, -, hD5, -⟩ := id hdisk
  have hmark := hdisk.faceDisk_inter_splitDiskImage_eq hcut hf₁
  have hrD : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ ⊆ tgtD (sK k) := fun k z hz =>
    ((hdisk.faceDisk_inter_vertexBallImage_eq ⟨(sK k, w), hwsK k⟩).symm.subset hz).1
  have hQE : ∀ e : Section34CompactEdgeIndex K K',
      closure (section34CompactSplitDiskImage srcBd f₁ e \
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ e) ⊆
        section34CompactSplitDiskImage src f₁ e := fun e =>
    (closure_minimal sdiff_subset
      (hcut.isPLCellOn_splitDiskImage hf₁ e).isPLSphere_one_of_two.isPolyhedron.isClosed).trans
      (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset
  have hedge : ∀ (k : Fin (m + 2)) (e : Section34CompactEdgeIndex K K'), w.1 ⊆ e.1 →
      Section34Incident e.1 (sK k).1 → ∃ l, e = eK l := fun k e hwe hes =>
    hecomp e ((convexHull_min hes (convex_convexHull ℝ _)).trans (hsb k)) hwe
  choose ρ hρ hρ1 hρ0 using hdisk.exists_faceArc_runs_of_edges hcut hf₁ hwsK hweK heinj hinc hedge
  have hQ : ∀ k : Fin (m + 2), ∃ σ : ℝ → E3, IsPLHomeomorphOn σ (Icc 0 1)
      (closure (section34CompactSplitDiskImage srcBd f₁ (eK k) \
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident (eK k).1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ (eK k))) ∧
      σ 0 = ρ k 1 ∧ σ 1 = ρ (k + 1) 0 := by
    intro k
    have heb : convexHull ℝ ((eK k).1 : Set E3) ⊆ frontier K.space :=
      (convexHull_min ((hinc k k).mpr (Or.inl rfl)) (convex_convexHull ℝ _)).trans (hsb k)
    obtain ⟨δ, hδ, hδb⟩ := hcut.exists_residual_outerArc hf₁ hdisk hR hDR hfr hint hio h7 h9
      (eK k) heb
    have hmarks : ({δ 0, δ 1} : Set E3) = {ρ k 1, ρ (k + 1) 0} := by
      rw [hδb]
      apply Subset.antisymm
      · intro y hy
        obtain ⟨p, ⟨hpe, hpb⟩, hyp⟩ := mem_iUnion₂.mp hy
        rw [← hmark] at hyp
        have hes : Section34Incident (eK k).1 p.1.1.1 := by
          rw [← hpe]
          exact p.2
        have hws : Section34Incident w.1 p.1.1.1 := fun z hz => hes (hweK k hz)
        obtain ⟨j, hj⟩ := hscomp p.1.1 hpb hws
        rw [hj, hpe] at hyp
        rw [hj] at hes
        rcases (hinc j k).mp hes with h | h
        · rw [← h, hρ1 k] at hyp
          exact Or.inl hyp
        · rw [← h, hρ0 (k + 1) k rfl] at hyp
          exact Or.inr hyp
      · rintro y (hy | hy)
        · refine mem_iUnion₂.mpr ⟨⟨(sK k, eK k), (hinc k k).mpr (Or.inl rfl)⟩,
            ⟨rfl, hsb k⟩, (hmark _).subset ?_⟩
          change y ∈ tgtD (sK k) ∩ section34CompactSplitDiskImage src f₁ (eK k)
          rw [hρ1 k, hy]
          exact mem_singleton _
        · refine mem_iUnion₂.mpr ⟨⟨(sK (k + 1), eK k), (hinc (k + 1) k).mpr (Or.inr rfl)⟩,
            ⟨rfl, hsb (k + 1)⟩, (hmark _).subset ?_⟩
          change y ∈ tgtD (sK (k + 1)) ∩ section34CompactSplitDiskImage src f₁ (eK k)
          rw [hρ0 (k + 1) k rfl, mem_singleton_iff.mp hy]
          exact mem_singleton _
    rcases Set.pair_eq_pair_iff.mp hmarks with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨δ, hδ, h0, h1⟩
    · obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ → E3, σ = fun x => δ (1 - x) := ⟨_, rfl⟩
      have hσ : IsPLHomeomorphOn σ (Icc 0 1)
          (closure (section34CompactSplitDiskImage srcBd f₁ (eK k) \
            ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident (eK k).1 t.1),
              Rf t ∩ section34CompactSplitDiskImage src f₁ (eK k))) := by
        rw [hσdef]
        exact isPLHomeomorphOn_comp_one_sub hδ
      have hσ0 : σ 0 = δ 1 := by
        rw [hσdef]
        norm_num
      have hσ1 : σ 1 = δ 0 := by
        rw [hσdef]
        norm_num
      exact ⟨σ, hσ, by rw [hσ0, h1], by rw [hσ1, h0]⟩
  choose σ hσ hσ0 hσ1 using hQ
  have hρm : ∀ k (x : ℝ), x ∈ Icc (0 : ℝ) 1 → ρ k x ∈ tgtA ⟨(sK k, w), hwsK k⟩ := fun k x hx =>
    (hρ k).bijOn.mapsTo hx
  have hσm : ∀ k (x : ℝ), x ∈ Icc (0 : ℝ) 1 →
      σ k x ∈ closure (section34CompactSplitDiskImage srcBd f₁ (eK k) \
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident (eK k).1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ (eK k)) := fun k x hx =>
    (hσ k).bijOn.mapsTo hx
  refine isPLSphere_one_iUnion_union_iUnion_of_cycle hρ hσ hσ0 hσ1 (fun k => ?_) (fun k => ?_)
    (fun k l hkl => (hD5 _ _ (hsinj.ne hkl)).mono (hrD k) (hrD l))
    (fun k l hkl => (hcut.disjoint_splitDiskImage hf₁ (heinj.ne hkl)).mono (hQE _) (hQE _))
    (fun k l h1 h2 => ?_)
  · apply Subset.antisymm
    · rintro z ⟨hzA, hzQ⟩
      rw [← hρ1 k]
      exact ⟨hrD k hzA, hQE _ hzQ⟩
    · rintro z hz
      rw [mem_singleton_iff.mp hz]
      exact ⟨hρm k 1 ⟨zero_le_one, le_rfl⟩, by rw [← hσ0 k]; exact hσm k 0 ⟨le_rfl, zero_le_one⟩⟩
  · apply Subset.antisymm
    · rintro z ⟨hzQ, hzA⟩
      rw [hσ1 k, ← hρ0 (k + 1) k rfl]
      exact ⟨hrD (k + 1) hzA, hQE _ hzQ⟩
    · rintro z hz
      rw [mem_singleton_iff.mp hz]
      refine ⟨hσm k 1 ⟨zero_le_one, le_rfl⟩, ?_⟩
      rw [hσ1 k]
      exact hρm (k + 1) 0 ⟨le_rfl, zero_le_one⟩
  · refine Set.disjoint_left.mpr fun z hzA hzQ => ?_
    have h0 : z ∈ tgtD (sK k) ∩ section34CompactSplitDiskImage src f₁ (eK l) :=
      ⟨hrD k hzA, hQE _ hzQ⟩
    rw [hdisk.faceDisk_inter_splitDiskImage_eq_empty hcut hf₁
      (fun h => ((hinc k l).mp h).elim h1 h2)] at h0
    exact h0

theorem closure_sdiff_eq_of_disk_pair {S D₀ D₁ J P : Set E3} {q₁ : (Fin 3 → ℝ) → E3}
    (hq₁ : IsPLHomeomorphOn q₁ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D₁)
    (hq₁J : q₁ '' stdSimplexBoundary 2 = J) (hD : D₀ ∪ D₁ = S) (hDi : D₀ ∩ D₁ = J)
    (hD₀P : D₀ ⊆ P) (hD₁P : Disjoint (D₁ \ J) P) : closure (S \ P) = D₁ := by
  have heq : S \ P = D₁ \ J := by
    apply Subset.antisymm
    · rintro z ⟨hzS, hzP⟩
      rw [← hD] at hzS
      rcases hzS with hz | hz
      · exact absurd (hD₀P hz) hzP
      · refine ⟨hz, fun hzJ => hzP (hD₀P ?_)⟩
        rw [← hDi] at hzJ
        exact hzJ.1
    · intro z hz
      refine ⟨?_, Set.disjoint_left.mp hD₁P hz⟩
      rw [← hD]
      exact Or.inr hz.1
  rw [heq, ← hq₁J]
  exact hq₁.closure_sdiff_image_stdSimplexBoundary (n := 1)

theorem Section34CompactCutFrame.exists_residual_outerDisk
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    (hdisk : Section34CompactFaceDiskFamily K K' (section34CompactVertexBallImage src f₁)
      (section34CompactSplitDiskImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {Rf : Section34CompactSimplexIndex K 4 → Set E3} (hR : ∀ t, IsPLBall 3 (Rf t))
    (hDR : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      Section34Incident s.1 t.1 → tgtD s ⊆ frontier (Rf t))
    (hfr : ∀ t : Section34CompactSimplexIndex K 4, frontier (Rf t) ⊆
      (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w) ∪
      ⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : ∀ t : Section34CompactSimplexIndex K 4, Disjoint (interior (Rf t))
      (⋃ (w : Section34CompactVertexIndex K K') (_ : Section34Incident w.1 t.1),
        section34CompactVertexBallImage src f₁ w))
    (hio : ∀ (t : Section34CompactSimplexIndex K 4) (a : Section34CompactArcIndex K K'),
      Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34CompactEdgeIndex K K', y ∉ section34CompactSplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∈ Rf t ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34CompactVertexBallImage src f₁ a.1.2) ∧ z ∉ Rf t)
    (h7 : ∀ (t : Section34CompactSimplexIndex K 4) (w : Section34CompactVertexIndex K K'),
      ¬ Section34Incident w.1 t.1 → Rf t ∩ section34CompactVertexBallImage src f₁ w = ∅)
    (h9 : ∀ (t : Section34CompactSimplexIndex K 4) (s : Section34CompactSimplexIndex K 3),
      ¬ Section34Incident s.1 t.1 → Rf t ∩ tgtD s = ∅)
    (w : Section34CompactVertexIndex K K') (hw : (w.1 : Set E3) ⊆ frontier K.space) :
    ∃ q : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (closure (frontier (section34CompactVertexBallImage src f₁ w) \
          ((⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
            section34CompactSplitDiskImage src f₁ e) ∪
          ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident w.1 t.1),
            Rf t ∩ section34CompactVertexBallImage src f₁ w))) ∧
      q '' stdSimplexBoundary 2 =
        (⋃ (a : Section34CompactArcIndex K K')
          (_ : a.1.2 = w ∧ convexHull ℝ (a.1.1.1 : Set E3) ⊆ frontier K.space), tgtA a) ∪
        ⋃ (e : Section34CompactEdgeIndex K K')
          (_ : convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space ∧ w.1 ⊆ e.1),
          closure (section34CompactSplitDiskImage srcBd f₁ e \
            ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
              Rf t ∩ section34CompactSplitDiskImage src f₁ e) := by
  obtain ⟨-, hKfin, hK'fin, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, hex⟩ := id hcut
  have _ := finite_section34CompactSimplexIndex hKfin 4
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 1
  have _ := finite_section34CompactGraphIndex hK'fin (section34CompactGraphSkeleton K) 2
  obtain ⟨hD1, -, -, -, -, -, hA7, hD8, -⟩ := id hdisk
  have hDc : ∀ s, IsClosed (tgtD s) := fun s => (hD1 s).isCompact.isClosed
  have hVball : ∀ u, IsPLBall 3 (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isPLBall_three
  have hVc : ∀ u, IsClosed (section34CompactVertexBallImage src f₁ u) := fun u =>
    (hVball u).isPolyhedron.isClosed
  have hEc : ∀ e, IsClosed (section34CompactSplitDiskImage src f₁ e) := fun e =>
    (hcut.isPLCellOn_splitDiskImage hf₁ e).isCompact.isClosed
  have hmark := hdisk.faceDisk_inter_splitDiskImage_eq hcut hf₁
  have hQEb : ∀ e : Section34CompactEdgeIndex K K',
      closure (section34CompactSplitDiskImage srcBd f₁ e \
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ e) ⊆
        section34CompactSplitDiskImage srcBd f₁ e := fun e =>
    closure_minimal sdiff_subset
      (hcut.isPLCellOn_splitDiskImage hf₁ e).isPLSphere_one_of_two.isPolyhedron.isClosed
  have hQE : ∀ e : Section34CompactEdgeIndex K K',
      closure (section34CompactSplitDiskImage srcBd f₁ e \
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ e) ⊆
        section34CompactSplitDiskImage src f₁ e := fun e =>
    (hQEb e).trans (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset
  obtain ⟨Cov, hCov⟩ : ∃ Cov : Set E3, Cov =
      (⋃ (e : Section34CompactEdgeIndex K K') (_ : w.1 ⊆ e.1),
        section34CompactSplitDiskImage src f₁ e) ∪
      ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident w.1 t.1),
        Rf t ∩ section34CompactVertexBallImage src f₁ w := ⟨_, rfl⟩
  obtain ⟨Jset, hJset⟩ : ∃ Jset : Set E3, Jset =
      (⋃ (a : Section34CompactArcIndex K K')
        (_ : a.1.2 = w ∧ convexHull ℝ (a.1.1.1 : Set E3) ⊆ frontier K.space), tgtA a) ∪
      ⋃ (e : Section34CompactEdgeIndex K K')
        (_ : convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space ∧ w.1 ⊆ e.1),
        closure (section34CompactSplitDiskImage srcBd f₁ e \
          ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
            Rf t ∩ section34CompactSplitDiskImage src f₁ e) := ⟨_, rfl⟩
  rw [← hCov, ← hJset]
  have hCovc : IsClosed Cov := by
    rw [hCov]
    exact (isClosed_iUnion_of_finite fun e => isClosed_iUnion_of_finite fun _ => hEc e).union
      (isClosed_iUnion_of_finite fun t => isClosed_iUnion_of_finite fun _ =>
        (hR t).isPolyhedron.isClosed.inter (hVc w))
  have hcapCov : ∀ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 →
      ∀ q ∈ section34CompactSplitDiskImage src f₁ e, q ∈ Cov := fun e he q hq => by
    rw [hCov]
    exact Or.inl (mem_iUnion₂.mpr ⟨e, he, hq⟩)
  have hpatchCov : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident w.1 t.1 →
      ∀ q ∈ Rf t, q ∈ section34CompactVertexBallImage src f₁ w → q ∈ Cov := fun t ht q hq hqV => by
    rw [hCov]
    exact Or.inr (mem_iUnion₂.mpr ⟨t, ht, hq, hqV⟩)
  have hAJ : ∀ a : Section34CompactArcIndex K K', a.1.2 = w →
      convexHull ℝ (a.1.1.1 : Set E3) ⊆ frontier K.space → tgtA a ⊆ Jset := fun a haw hab z hz => by
    rw [hJset]
    exact Or.inl (mem_iUnion₂.mpr ⟨a, ⟨haw, hab⟩, hz⟩)
  have hQJ : ∀ e : Section34CompactEdgeIndex K K',
      convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space → w.1 ⊆ e.1 →
      closure (section34CompactSplitDiskImage srcBd f₁ e \
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ e) ⊆ Jset := fun e heb hwe z hz => by
    rw [hJset]
    exact Or.inr (mem_iUnion₂.mpr ⟨e, ⟨heb, hwe⟩, hz⟩)
  have hmarkQ : ∀ (e : Section34CompactEdgeIndex K K') (s : Section34CompactSimplexIndex K 3),
      convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space → Section34Incident e.1 s.1 →
      convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space → ∀ z ∈ tgtD s,
      z ∈ section34CompactSplitDiskImage src f₁ e →
      z ∈ closure (section34CompactSplitDiskImage srcBd f₁ e \
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident e.1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ e) := by
    intro e s heb hes hsb z hzD hzE
    obtain ⟨δ, hδ, hδb⟩ := hcut.exists_residual_outerArc hf₁ hdisk hR hDR hfr hint hio h7 h9 e heb
    have hz : z ∈ ({δ 0, δ 1} : Set E3) := by
      rw [hδb]
      exact mem_iUnion₂.mpr ⟨⟨(s, e), hes⟩, ⟨rfl, hsb⟩, (hmark _).subset ⟨hzD, hzE⟩⟩
    rcases hz with hz | hz
    · rw [hz]
      exact hδ.bijOn.mapsTo ⟨le_rfl, zero_le_one⟩
    · rw [mem_singleton_iff.mp hz]
      exact hδ.bijOn.mapsTo ⟨zero_le_one, le_rfl⟩
  have hArc : ∀ a : Section34CompactArcIndex K K', a.1.2 = w →
      tgtA a ⊆ tgtD a.1.1 ∩ frontier (section34CompactVertexBallImage src f₁ w) := by
    intro a haw z hz
    have hz' : z ∈ tgtDBd a.1.1 ∩ section34CompactVertexBallImage src f₁ a.1.2 :=
      (hA7 a).symm.subset hz
    rw [haw] at hz'
    exact ⟨(hD1 a.1.1).boundary_subset hz'.1, subset_closure hz'.2, fun hzi =>
      (hdisk.2.2.2.1 a.1.1 hz'.1).2 (interior_mono (subset_iUnion _ w) hzi)⟩
  have hJS : Jset ⊆ frontier (section34CompactVertexBallImage src f₁ w) := by
    rw [hJset]
    refine union_subset (iUnion₂_subset fun a ha => (hArc a ha.1).trans inter_subset_right)
      (iUnion₂_subset fun e he => (hQE e).trans (hcut.splitDiskImage_subset_frontier hf₁ he.2))
  obtain ⟨m, sK, eK, hsb, hwsK, hweK, hsinj, heinj, hinc, hscomp, hecomp⟩ :=
    hcut.exists_outerEnum hw
  have hJ := hcut.isPLSphere_outerCircle hf₁ hdisk hR hDR hfr hint hio h7 h9 hsb hwsK hweK
    hsinj heinj hinc hscomp hecomp
  have heKb : ∀ k, convexHull ℝ ((eK k).1 : Set E3) ⊆ frontier K.space := fun k =>
    (convexHull_min ((hinc k k).mpr (Or.inl rfl)) (convex_convexHull ℝ _)).trans (hsb k)
  have hJeq : (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
      ⋃ k, closure (section34CompactSplitDiskImage srcBd f₁ (eK k) \
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : Section34Incident (eK k).1 t.1),
          Rf t ∩ section34CompactSplitDiskImage src f₁ (eK k)) = Jset := by
    rw [hJset]
    congr 1
    · ext y
      simp only [mem_iUnion, exists_prop]
      constructor
      · rintro ⟨k, hy⟩
        exact ⟨⟨(sK k, w), hwsK k⟩, ⟨rfl, hsb k⟩, hy⟩
      · rintro ⟨a, ⟨haw, hab⟩, hy⟩
        have hwa : Section34Incident w.1 a.1.1.1 := by
          rw [← haw]
          exact a.2
        obtain ⟨k, hk⟩ := hscomp a.1.1 hab hwa
        have ha : a = ⟨(sK k, w), hwsK k⟩ := Subtype.ext (Prod.ext hk haw)
        rw [ha] at hy
        exact ⟨k, hy⟩
    · ext y
      simp only [mem_iUnion, exists_prop]
      constructor
      · rintro ⟨k, hy⟩
        exact ⟨eK k, ⟨heKb k, hweK k⟩, hy⟩
      · rintro ⟨e, ⟨heb, hwe⟩, hy⟩
        obtain ⟨k, rfl⟩ := hecomp e heb hwe
        exact ⟨k, hy⟩
  rw [hJeq] at hJ
  obtain ⟨D₀, D₁, q₀, q₁, hq₀, hq₁, hq₀J, hq₁J, hDU, hDI⟩ :=
    exists_isPLBall_pair_of_isPLSphere_two (hVball w).isPLSphere_frontier hJ hJS
  have hloc : ∀ z ∈ frontier (section34CompactVertexBallImage src f₁ w), z ∈ Cov → z ∉ Jset →
      ∃ U ∈ 𝓝 z, U ∩ frontier (section34CompactVertexBallImage src f₁ w) ⊆ Cov := by
    intro z hzS hz hzJ
    by_cases hzcap : ∃ e : Section34CompactEdgeIndex K K', w.1 ⊆ e.1 ∧
        z ∈ section34CompactSplitDiskImage src f₁ e
    · obtain ⟨e, hwe, hzE⟩ := hzcap
      obtain ⟨w', hww', hw'e⟩ : ∃ w' : Section34CompactVertexIndex K K', w ≠ w' ∧
          w'.1 ⊆ e.1 := by
        obtain ⟨a, b, hab, habe, -⟩ := hcut.splitDiskImage_eq_inter hf₁ e
        have hae : a.1 ⊆ e.1 := by
          have h : (a.1 : Set E3) ⊆ e.1 := by
            rw [habe]
            exact subset_union_left
          exact Finset.coe_subset.mp h
        have hbe : b.1 ⊆ e.1 := by
          have h : (b.1 : Set E3) ⊆ e.1 := by
            rw [habe]
            exact subset_union_right
          exact Finset.coe_subset.mp h
        rcases eq_or_eq_of_section34CompactVertexIndex_subset e habe hwe with h | h
        · exact ⟨b, by rw [h]; exact hab, hbe⟩
        · exact ⟨a, by rw [h]; exact hab.symm, hae⟩
      have hinter := hcut.vertexBallImage_inter_eq_splitDiskImage hf₁ hww' hwe hw'e
      have hEcap : ∀ q ∈ frontier (section34CompactVertexBallImage src f₁ w),
          q ∈ section34CompactVertexBallImage src f₁ w' → q ∈ Cov := fun q hq hqw' =>
        hcapCov e hwe q (by rw [← hinter]; exact ⟨(hVc w).frontier_subset hq, hqw'⟩)
      by_cases hzb : z ∈ section34CompactSplitDiskImage srcBd f₁ e
      · obtain ⟨t, het, hzR, hzs⟩ : ∃ t : Section34CompactSimplexIndex K 4,
            Section34Incident e.1 t.1 ∧ z ∈ Rf t ∧ ∀ s : Section34CompactSimplexIndex K 3,
              Section34Incident e.1 s.1 → z ∈ tgtD s →
                ¬ convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space := by
          by_cases hei : convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space
          · have hzU : z ∈ ⋃ (t : Section34CompactSimplexIndex K 4)
                (_ : Section34Incident e.1 t.1),
                  Rf t ∩ section34CompactSplitDiskImage src f₁ e := by
              by_contra hzU
              exact hzJ (hQJ e hei hwe (subset_closure ⟨hzb, hzU⟩))
            obtain ⟨t, het, hzR, -⟩ := mem_iUnion₂.mp hzU
            exact ⟨t, het, hzR, fun s hes hzs hsb =>
              hzJ (hQJ e hei hwe (hmarkQ e s hei hes hsb z hzs hzE))⟩
          · obtain ⟨t, het, hzR, -⟩ := mem_iUnion₂.mp
              (hcut.splitDiskImage_boundary_subset_iUnion_residual hf₁ hdisk hR hDR hfr hint hio
                h7 h9 e hei hzb)
            exact ⟨t, het, hzR, fun s hes _ h =>
              hei ((convexHull_min hes (convex_convexHull ℝ _)).trans h)⟩
        obtain ⟨U, hU, hUR⟩ := hcut.exists_mem_nhds_frontier_pair_subset_iUnion_residual hf₁
          hdisk hR hDR hfr hint hio h7 h9 hww' hwe hw'e hzb hzs het hzR
        refine ⟨U, hU, fun q hq => ?_⟩
        by_cases hqw' : q ∈ section34CompactVertexBallImage src f₁ w'
        · exact hEcap q hq.2 hqw'
        · obtain ⟨t', het', hqR⟩ := mem_iUnion₂.mp
            (hUR ⟨hq.1, mem_frontier_union_of_notMem (hVc w') hq.2 hqw'⟩)
          exact hpatchCov t' (fun x hx => het' (hwe hx)) q hqR ((hVc w).frontier_subset hq.2)
      · have hzi : z ∈ interior (⋃ u, section34CompactVertexBallImage src f₁ u) :=
          hcut.splitDiskImage_sdiff_subset_interior hf₁ e ⟨hzE, hzb⟩
        have hFc : IsClosed (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
            section34CompactVertexBallImage src f₁ u) :=
          isClosed_iUnion_of_finite fun u => isClosed_iUnion_of_finite fun _ => hVc u
        have hzww : z ∈ section34CompactVertexBallImage src f₁ w ∩
            section34CompactVertexBallImage src f₁ w' := by
          rw [hinter]
          exact hzE
        have hzF : z ∉ ⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
            section34CompactVertexBallImage src f₁ u := by
          intro h
          obtain ⟨u, ⟨huw, huw'⟩, hzu⟩ := mem_iUnion₂.mp h
          have h0 : z ∈ section34CompactVertexBallImage src f₁ u ∩
              section34CompactVertexBallImage src f₁ w ∩
              section34CompactVertexBallImage src f₁ w' := ⟨⟨hzu, hzww.1⟩, hzww.2⟩
          rw [hcut.vertexBallImage_inter_inter_eq_empty hf₁ huw huw' hww'] at h0
          exact h0
        refine ⟨interior (⋃ u, section34CompactVertexBallImage src f₁ u) ∩
          (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
            section34CompactVertexBallImage src f₁ u)ᶜ,
          (isOpen_interior.inter hFc.isOpen_compl).mem_nhds ⟨hzi, hzF⟩, fun q hq => ?_⟩
        by_cases hqw' : q ∈ section34CompactVertexBallImage src f₁ w'
        · exact hEcap q hq.2 hqw'
        · exfalso
          refine hq.2.2 (mem_interior.mpr
            ⟨interior (⋃ u, section34CompactVertexBallImage src f₁ u) ∩
            (⋃ (u : Section34CompactVertexIndex K K') (_ : u ≠ w ∧ u ≠ w'),
              section34CompactVertexBallImage src f₁ u)ᶜ ∩
            (section34CompactVertexBallImage src f₁ w')ᶜ, fun y hy => ?_,
            (isOpen_interior.inter hFc.isOpen_compl).inter (hVc w').isOpen_compl,
            ⟨hq.1, hqw'⟩⟩)
          obtain ⟨⟨hy1, hy2⟩, hy3⟩ := hy
          obtain ⟨u, hyu⟩ := mem_iUnion.mp (interior_subset hy1)
          by_cases huw : u = w
          · rw [← huw]
            exact hyu
          · by_cases huw' : u = w'
            · rw [huw'] at hyu
              exact absurd hyu hy3
            · exact absurd (mem_iUnion₂.mpr ⟨u, ⟨huw, huw'⟩, hyu⟩) hy2
    · rw [hCov] at hz
      rcases hz with hz | hz
      · obtain ⟨e, he, hzE⟩ := mem_iUnion₂.mp hz
        exact absurd ⟨e, he, hzE⟩ hzcap
      · obtain ⟨t, htw, hzR, hzV⟩ := mem_iUnion₂.mp hz
        have hzV' : ∀ u, z ∈ section34CompactVertexBallImage src f₁ u →
            section34CompactVertexBallImage src f₁ u ⊆
              section34CompactVertexBallImage src f₁ w := by
          intro u hzu
          by_cases huw : u = w
          · exact (congrArg (section34CompactVertexBallImage src f₁) huw).subset
          · exfalso
            obtain ⟨e, hze⟩ := hcut.exists_mem_splitDiskImage_of_ne hf₁ huw hzu hzV
            exact hzcap ⟨e, hcut.subset_of_mem_splitDiskImage hf₁ hze hzV, hze⟩
        by_cases hzD : ∃ s, z ∈ tgtD s
        · obtain ⟨s, hzs⟩ := hzD
          have hws : Section34Incident w.1 s.1 := by
            by_contra hws
            have h0 : z ∈ tgtD s ∩ section34CompactVertexBallImage src f₁ w := ⟨hzs, hzV⟩
            rw [hD8 s w hws] at h0
            exact h0
          have hsi : ¬ convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space := fun hsb =>
            hzJ (hAJ ⟨(s, w), hws⟩ rfl hsb
              ((hdisk.faceDisk_inter_vertexBallImage_eq ⟨(s, w), hws⟩).subset ⟨hzs, hzV⟩))
          obtain ⟨t₁, t₂, ht12, hs1, hs2⟩ := hcut.exists_tetra_pair_of_not_boundary_triangle s hsi
          have hw1 : Section34Incident w.1 t₁.1 := fun x hx =>
            convexHull_min hs1 (convex_convexHull ℝ _) (hws hx)
          have hw2 : Section34Incident w.1 t₂.1 := fun x hx =>
            convexHull_min hs2 (convex_convexHull ℝ _) (hws hx)
          have hRW := hcut.isPLBall_residual_union_vertexBallImage hf₁ hdisk (hR t₁) (hDR t₁)
            (hfr t₁) (hint t₁) (hio t₁) (h7 t₁) hw1
          obtain ⟨U, hU, hUR⟩ := hcut.exists_mem_nhds_frontier_subset_union hf₁ hdisk hR hDR hfr
            hint h7 h9 ht12 hs1 hs2 (subset_iUnion₂_of_subset w hw2 subset_rfl) hRW hzs hzV'
          refine ⟨U, hU, fun q hq => ?_⟩
          rcases hUR hq with h | h
          · exact hpatchCov t₁ hw1 q h ((hVc w).frontier_subset hq.2)
          · exact hpatchCov t₂ hw2 q h ((hVc w).frontier_subset hq.2)
        · obtain ⟨U, hU, hUR, -⟩ := hcut.exists_mem_nhds_frontier_subset_residual hf₁ (hR t)
            (hfr t) (hint t) hDc (hVball w) (subset_iUnion₂_of_subset w htw subset_rfl) hzR hzS
            (fun u _ hzu => hzV' u hzu) (fun s _ hzs => hzD ⟨s, hzs⟩)
          exact ⟨U, hU, fun q hq =>
            hpatchCov t htw q (hUR hq) ((hVc w).frontier_subset hq.2)⟩
  have hDS : ∀ {D : Set E3}, D ⊆ D₀ ∪ D₁ →
      D ⊆ frontier (section34CompactVertexBallImage src f₁ w) :=
    fun hD => hD.trans hDU.subset
  have hside : ∀ (D : Set E3) (q : (Fin 3 → ℝ) → E3), IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D →
      q '' stdSimplexBoundary 2 = Jset → D ⊆ D₀ ∪ D₁ →
      D \ q '' stdSimplexBoundary 2 ⊆ Cov ∨ Disjoint (D \ q '' stdSimplexBoundary 2) Cov := by
    intro D q hq hqJ hDsub
    refine subset_or_disjoint_of_isPreconnected_of_locally_subset
      (hq.isConnected_sdiff_image_stdSimplexBoundary (n := 1)).isPreconnected hCovc
      fun y hy hyC => ?_
    obtain ⟨U, hU, hUC⟩ := hloc y (hDS hDsub hy.1) hyC (by rw [← hqJ]; exact hy.2)
    exact ⟨U, hU, fun x hx => hUC ⟨hx.1, hDS hDsub hx.2.1⟩⟩
  have hD0 := hside D₀ q₀ hq₀ hq₀J subset_union_left
  have hD1 := hside D₁ q₁ hq₁ hq₁J subset_union_right
  have hcl : ∀ (D : Set E3) (q : (Fin 3 → ℝ) → E3), IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D →
      D \ q '' stdSimplexBoundary 2 ⊆ Cov → D ⊆ Cov := fun D q hq h z hz => by
    rw [← hq.closure_sdiff_image_stdSimplexBoundary (n := 1)] at hz
    exact closure_minimal h hCovc hz
  rcases hD0 with hD0 | hD0 <;> rcases hD1 with hD1 | hD1
  · exfalso
    obtain ⟨y₀, hy₀A, hy₀E⟩ := hdisk.exists_mem_faceArc_notMem_splitDiskImage ⟨(sK 0, w), hwsK 0⟩
    obtain ⟨t₀, hst₀⟩ := hex (sK 0)
    have hy₀D : y₀ ∈ tgtD (sK 0) :=
      ((hdisk.faceDisk_inter_vertexBallImage_eq ⟨(sK 0, w), hwsK 0⟩).symm.subset hy₀A).1
    have hFc : IsClosed ((⋃ e, section34CompactSplitDiskImage src f₁ e) ∪
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : t ≠ t₀), Rf t) :=
      (isClosed_iUnion_of_finite fun e => hEc e).union
        (isClosed_iUnion_of_finite fun t => isClosed_iUnion_of_finite fun _ =>
          (hR t).isPolyhedron.isClosed)
    have hy₀F : y₀ ∉ (⋃ e, section34CompactSplitDiskImage src f₁ e) ∪
        ⋃ (t : Section34CompactSimplexIndex K 4) (_ : t ≠ t₀), Rf t := by
      rintro (h | h)
      · obtain ⟨e, he⟩ := mem_iUnion.mp h
        exact hy₀E e he
      · obtain ⟨t, htt, hy₀R⟩ := mem_iUnion₂.mp h
        have hs0t : ¬ Section34Incident (sK 0).1 t.1 := fun h' =>
          htt (hcut.tetra_eq_of_boundary_triangle (sK 0) (hsb 0) h' hst₀)
        have h0 : y₀ ∈ Rf t ∩ tgtD (sK 0) := ⟨hy₀R, hy₀D⟩
        rw [h9 t (sK 0) hs0t] at h0
        exact h0
    obtain ⟨-, z, hzU, hzS, hzR⟩ :=
      hio t₀ ⟨(sK 0, w), hwsK 0⟩ hst₀ y₀ hy₀A hy₀E _ (hFc.isOpen_compl.mem_nhds hy₀F)
    have hzS' : z ∈ D₀ ∪ D₁ := hDU.symm.subset hzS
    have hzC : z ∈ Cov := by
      rcases hzS' with hz | hz
      · exact hcl D₀ q₀ hq₀ hD0 hz
      · exact hcl D₁ q₁ hq₁ hD1 hz
    rw [hCov] at hzC
    rcases hzC with hz | hz
    · obtain ⟨e, -, hze⟩ := mem_iUnion₂.mp hz
      exact hzU (Or.inl (mem_iUnion.mpr ⟨e, hze⟩))
    · obtain ⟨t, -, hzR', -⟩ := mem_iUnion₂.mp hz
      by_cases htt : t = t₀
      · rw [htt] at hzR'
        exact hzR hzR'
      · exact hzU (Or.inr (mem_iUnion₂.mpr ⟨t, htt, hzR'⟩))
  · refine ⟨q₁, ?_, hq₁J⟩
    rw [closure_sdiff_eq_of_disk_pair hq₁ hq₁J hDU hDI (hcl D₀ q₀ hq₀ hD0)
      (by rw [← hq₁J]; exact hD1)]
    exact hq₁
  · refine ⟨q₀, ?_, hq₀J⟩
    rw [closure_sdiff_eq_of_disk_pair hq₀ hq₀J (by rw [union_comm]; exact hDU)
      (by rw [inter_comm]; exact hDI) (hcl D₁ q₁ hq₁ hD1) (by rw [← hq₀J]; exact hD0)]
    exact hq₀
  · exfalso
    obtain ⟨e, hwe⟩ := hcut.exists_edgeIndex_of_vertex w
    obtain ⟨qE, hqE, hqEb⟩ :=
      (hcut.isPLCellOn_splitDiskImage hf₁ e).exists_isPLHomeomorphOn_stdSimplex
    obtain ⟨z, hz⟩ := (hqE.isConnected_sdiff_image_stdSimplexBoundary (n := 1)).nonempty
    have hz' : z ∈ section34CompactSplitDiskImage src f₁ e \
        section34CompactSplitDiskImage srcBd f₁ e := by
      rw [hqEb]
      exact hz
    have hzC := hcapCov e hwe z hz'.1
    have hzJ : z ∉ Jset := by
      rw [hJset]
      rintro (hzJ | hzJ)
      · obtain ⟨a, ⟨haw, -⟩, hza⟩ := mem_iUnion₂.mp hzJ
        exact hz'.2 (hdisk.faceDisk_inter_splitDiskImage_subset hcut hf₁ a.1.1 e
          ⟨(hArc a haw hza).1, hz'.1⟩).2
      · obtain ⟨e', -, hze'⟩ := mem_iUnion₂.mp hzJ
        have hee : e' = e := by
          by_contra h
          exact Set.disjoint_left.mp (hcut.disjoint_splitDiskImage hf₁ h) (hQE e' hze') hz'.1
        rw [hee] at hze'
        exact hz'.2 (hQEb e hze')
    have hzS : z ∈ D₀ ∪ D₁ :=
      hDU.symm.subset (hcut.splitDiskImage_subset_frontier hf₁ hwe hz'.1)
    rcases hzS with hz0 | hz1
    · exact Set.disjoint_left.mp hD0 ⟨hz0, by rw [hq₀J]; exact hzJ⟩ hzC
    · exact Set.disjoint_left.mp hD1 ⟨hz1, by rw [hq₁J]; exact hzJ⟩ hzC

end DifferentialGeometry.Topology.PiecewiseLinear
