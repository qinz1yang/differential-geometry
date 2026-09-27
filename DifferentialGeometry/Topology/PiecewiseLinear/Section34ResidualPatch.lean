/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ResidualPatchSides
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellChartCircleRuns

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
  {fbl fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}

theorem Section34FaceDiskFamily.exists_faceArc_endpoints
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34SimplexIndex 𝒦 4} {w : Section34VertexIndex 𝒦 𝒦'} {m : ℕ}
    {sK : Fin (m + 2) → Section34SimplexIndex 𝒦 3}
    {eK : Fin (m + 2) → Section34EdgeIndex 𝒦 𝒦'}
    (hsK : ∀ k, Section34Incident (sK k).1 t.1) (hwsK : ∀ k, Section34Incident w.1 (sK k).1)
    (hweK : ∀ k, w.1 ⊆ (eK k).1) (heinj : Function.Injective eK)
    (hinc : ∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k)
    (hecomp : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 → w.1 ⊆ e.1 →
      ∃ k, e = eK k) (k : Fin (m + 2)) :
    ∃ p q : M₂, IsPLCellOn 1 (tgtA ⟨(sK k, w), hwsK k⟩) {q, p} ∧
      tgtD (sK k) ∩ section34SplitDiskImage src f₁ (eK k) = {p} ∧
      ∀ l, l + 1 = k → tgtD (sK k) ∩ section34SplitDiskImage src f₁ (eK l) = {q} := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  obtain ⟨-, -, -, -, -, hA6, -, -, -, -, -, hA12⟩ := id hdisk
  have hEsub : ∀ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 →
      section34SplitDiskImage src f₁ e ⊆ section34VertexBallImage src f₁ w :=
    fun e he => (hcut.splitDiskImage_subset_frontier hf₁ he).trans
      (hcut.isPLCellOn_vertexBallImage hf₁ w).isCompact.isClosed.frontier_subset
  have hrV : tgtA ⟨(sK k, w), hwsK k⟩ =
      tgtD (sK k) ∩ section34VertexBallImage src f₁ w :=
    (hdisk.faceDisk_inter_vertexBall_eq ⟨(sK k, w), hwsK k⟩).symm
  obtain ⟨p, hp, -⟩ := hdisk.exists_faceDisk_inter_splitDisk_eq_singleton hdata (sK k)
    (eK k) ((hinc k k).mpr (Or.inl rfl))
  obtain ⟨q, hq, -⟩ := hdisk.exists_faceDisk_inter_splitDisk_eq_singleton hdata (sK k)
    (eK (k - 1)) ((hinc k (k - 1)).mpr (Or.inr (sub_add_cancel k 1)))
  have hpred : ∀ l, l + 1 = k → l = k - 1 := fun l hl => by rw [← hl, add_sub_cancel_right]
  have hpD : p ∈ tgtD (sK k) := (hp.symm.subset (mem_singleton p)).1
  have hpE : p ∈ section34SplitDiskImage src f₁ (eK k) :=
    (hp.symm.subset (mem_singleton p)).2
  have hqD : q ∈ tgtD (sK k) := (hq.symm.subset (mem_singleton q)).1
  have hqE : q ∈ section34SplitDiskImage src f₁ (eK (k - 1)) :=
    (hq.symm.subset (mem_singleton q)).2
  have hne : k - 1 ≠ k := fun h => one_ne_zero (sub_eq_self.mp h)
  have hqp : q ≠ p := fun h => Set.disjoint_left.mp
    (hcut.disjoint_splitDiskImage hf₁.injOn (heinj.ne hne)) hqE (by rw [h]; exact hpE)
  have hbd : tgtABd ⟨(sK k, w), hwsK k⟩ = {q, p} := by
    rw [hA12, hrV]
    apply Subset.antisymm
    · rintro z ⟨⟨hzD, hzV⟩, hzE⟩
      obtain ⟨e, hze⟩ := mem_iUnion.mp hzE
      have hwe := hcut.subset_of_mem_splitDiskImage hf₁.injOn hze hzV
      have hse : Section34Incident e.1 (sK k).1 := by
        by_contra hse
        have h0 : z ∈ tgtD (sK k) ∩ section34SplitDiskImage src f₁ e := ⟨hzD, hze⟩
        rw [hdisk.faceDisk_inter_splitDisk_eq_empty hdata hse] at h0
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
  refine ⟨p, q, ?_, hp, fun l hl => by rw [hpred l hl]; exact hq⟩
  have hc := hA6 ⟨(sK k, w), hwsK k⟩
  rwa [hbd] at hc

theorem Section34NormalPlus.isPLCellOn_residualPatch
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁
      (section34VertexBallImage src f₁) (section34VertexBallImage srcBd f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (section34VertexBallImage src f₁)
      (section34SplitDiskImage src f₁) (section34SplitDiskImage srcBd f₁)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {t : Section34SimplexIndex 𝒦 4} {R : Set M₂} (hR : IsPLCellOn 3 R (frontier R))
    (hDR : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      tgtD s ⊆ frontier R)
    (hfr : frontier R ⊆ (⋃ (w : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident w.1 t.1),
        section34VertexBallImage src f₁ w) ∪
      ⋃ (s : Section34SimplexIndex 𝒦 3) (_ : Section34Incident s.1 t.1), tgtD s)
    (hint : Disjoint (interior R) (⋃ (w : Section34VertexIndex 𝒦 𝒦')
      (_ : Section34Incident w.1 t.1), section34VertexBallImage src f₁ w))
    (hio : ∀ a : Section34ArcIndex 𝒦 𝒦', Section34Incident a.1.1.1 t.1 → ∀ y ∈ tgtA a,
      (∀ e : Section34EdgeIndex 𝒦 𝒦', y ∉ section34SplitDiskImage src f₁ e) →
      ∀ U ∈ 𝓝 y,
        (∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∈ R ∧
          z ∉ tgtD a.1.1) ∧
        ∃ z ∈ U, z ∈ frontier (section34VertexBallImage src f₁ a.1.2) ∧ z ∉ R)
    (h7 : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
      R ∩ section34VertexBallImage src f₁ w = ∅)
    {w : Section34VertexIndex 𝒦 𝒦'} {m : ℕ}
    {sK : Fin (m + 2) → Section34SimplexIndex 𝒦 3}
    {eK : Fin (m + 2) → Section34EdgeIndex 𝒦 𝒦'}
    (hsK : ∀ k, Section34Incident (sK k).1 t.1) (hwsK : ∀ k, Section34Incident w.1 (sK k).1)
    (hweK : ∀ k, w.1 ⊆ (eK k).1) (hsinj : Function.Injective sK)
    (heinj : Function.Injective eK)
    (hinc : ∀ k l, Section34Incident (eK l).1 (sK k).1 ↔ l = k ∨ l + 1 = k)
    (hscomp : ∀ s : Section34SimplexIndex 𝒦 3, Section34Incident s.1 t.1 →
      Section34Incident w.1 s.1 → ∃ k, s = sK k)
    (hecomp : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 t.1 → w.1 ⊆ e.1 →
      ∃ k, e = eK k) :
    IsPLCellOn 2 (R ∩ section34VertexBallImage src f₁ w)
      ((⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
        ⋃ k, R ∩ section34SplitDiskImage src f₁ (eK k)) ∧
    ∀ k, IsPLCellOn 1 (R ∩ section34SplitDiskImage src f₁ (eK k))
      ((tgtD (sK k) ∩ section34SplitDiskImage src f₁ (eK k)) ∪
        tgtD (sK (k + 1)) ∩ section34SplitDiskImage src f₁ (eK k)) := by
  have hcut := hdata.1
  have hf₁ := hdata.2.2.1.2.2.1
  have hw : Section34Incident w.1 t.1 := fun z hz =>
    convexHull_min (hsK 0) (convex_convexHull ℝ _) (hwsK 0 hz)
  have heKt : ∀ k, Section34Incident (eK k).1 t.1 := fun k z hz =>
    convexHull_min (hsK k) (convex_convexHull ℝ _) (((hinc k k).mpr (Or.inl rfl)) hz)
  have hVc : ∀ u, IsClosed (section34VertexBallImage src f₁ u) := fun u =>
    (hcut.isPLCellOn_vertexBallImage hf₁ u).isCompact.isClosed
  obtain ⟨-, -, -, hD4, hD5, -, hA7, -⟩ := id hdisk
  have hEsub : ∀ e : Section34EdgeIndex 𝒦 𝒦', w.1 ⊆ e.1 →
      section34SplitDiskImage src f₁ e ⊆ section34VertexBallImage src f₁ w :=
    fun e he => (hcut.splitDiskImage_subset_frontier hf₁ he).trans (hVc w).frontier_subset
  have hrV : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ =
      tgtD (sK k) ∩ section34VertexBallImage src f₁ w := fun k =>
    (hdisk.faceDisk_inter_vertexBall_eq ⟨(sK k, w), hwsK k⟩).symm
  have hrD : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ ⊆ tgtD (sK k) := fun k z hz => ((hrV k).subset hz).1
  choose p q hA hp hq using
    hdisk.exists_faceArc_endpoints hdata hsK hwsK hweK heinj hinc hecomp
  have hmarkb : ∀ k l, ∀ x, tgtD (sK k) ∩ section34SplitDiskImage src f₁ (eK l) = {x} →
      x ∈ section34SplitDiskImage srcBd f₁ (eK l) := by
    intro k l x hx
    exact (hdisk.faceDisk_inter_splitDisk_subset hdata (sK k) (eK l)
      (hx.symm.subset (mem_singleton x))).2
  have hrB : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ ⊆
      frontier (section34VertexBallImage src f₁ w) := by
    intro k z hz
    have hz' : z ∈ tgtDBd (sK k) ∩ section34VertexBallImage src f₁ w :=
      (hA7 ⟨(sK k, w), hwsK k⟩).symm.subset hz
    exact ⟨subset_closure hz'.2, fun hzi =>
      (hD4 (sK k) hz'.1).2 (interior_mono (subset_iUnion _ w) hzi)⟩
  have hout : ∀ k, tgtA ⟨(sK k, w), hwsK k⟩ ∩ section34SplitDiskImage src f₁ (eK k) =
      {p k} := fun k => by
    rw [hrV k, inter_assoc, inter_eq_right.mpr (hEsub _ (hweK k)), hp k]
  have hin : ∀ k, tgtA ⟨(sK (k + 1), w), hwsK (k + 1)⟩ ∩
      section34SplitDiskImage src f₁ (eK k) = {q (k + 1)} := fun k => by
    rw [hrV (k + 1), inter_assoc, inter_eq_right.mpr (hEsub _ (hweK k)), hq (k + 1) k rfl]
  have hfar : ∀ k l, l ≠ k → l + 1 ≠ k →
      tgtA ⟨(sK k, w), hwsK k⟩ ∩ section34SplitDiskImage src f₁ (eK l) = ∅ := by
    intro k l hlk hlk'
    rw [hrV k, inter_assoc, inter_eq_right.mpr (hEsub _ (hweK l)),
      hdisk.faceDisk_inter_splitDisk_eq_empty hdata
        (fun h => ((hinc k l).mp h).elim hlk hlk')]
  obtain ⟨c, hc, -, hVchart, -⟩ := hdata.exists_chart_tetrahedron t
  obtain ⟨X, Xb, Y, Yb, hX, hY, hXY, hXYi, hHk, hXb, hYb, hI⟩ :=
    (hcut.isPLCellOn_vertexBallImage hf₁ w).exists_split_of_runs_in_chart
      (fun k => hcut.isPLCellOn_splitDiskImage hf₁ (eK k))
      (fun k => hcut.splitDiskImage_subset_frontier hf₁ (hweK k))
      (fun k l hkl => hcut.disjoint_splitDiskImage hf₁.injOn (heinj.ne hkl)) hA hrB
      (fun k l hkl => (hD5 _ _ (hsinj.ne hkl)).mono (hrD k) (hrD l)) hout hin hfar
      (fun k => hmarkb k k _ (hp k)) (fun k => hmarkb (k + 1) k _ (hq (k + 1) k rfl))
      hc (hVchart w hw)
  have hkey : ∃ A Ab : Set M₂, IsPLCellOn 2 A Ab ∧
      Ab = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
        ⋃ k, A ∩ section34SplitDiskImage src f₁ (eK k) ∧
      R ∩ section34VertexBallImage src f₁ w = A ∧
      (∀ k, R ∩ section34SplitDiskImage src f₁ (eK k) =
        A ∩ section34SplitDiskImage src f₁ (eK k)) ∧
      ∀ k, IsPLCellOn 1 (A ∩ section34SplitDiskImage src f₁ (eK k))
        {p k, q (k + 1)} := by
    rcases hdata.residual_sides hdisk hR hDR hfr hint hio h7 hsK hwsK hsinj hscomp hecomp
      hX hY hXY hXb hYb with ⟨hXR, hYR⟩ | ⟨hYR, hXR⟩
    · obtain ⟨hRV, hRE⟩ := hdata.residual_inter_vertexBallImage_eq_of_sides hdisk hR hfr
        hint h7 hw hwsK hweK heKt hscomp hX hY hXY hXYi hHk hYb hXR hYR
      exact ⟨X, Xb, hX, hXb, hRV, hRE, fun k => (hI k).1⟩
    · have hYX : Y ∪ X ∪ (⋃ k, section34SplitDiskImage src f₁ (eK k)) =
          frontier (section34VertexBallImage src f₁ w) := by
        rw [union_comm Y X]
        exact hXY
      have hYXi : Y ∩ X = ⋃ k, tgtA ⟨(sK k, w), hwsK k⟩ := by
        rw [inter_comm]
        exact hXYi
      have hHk' : ∀ k, Y ∩ section34SplitDiskImage src f₁ (eK k) ∪
          X ∩ section34SplitDiskImage src f₁ (eK k) =
            section34SplitDiskImage srcBd f₁ (eK k) := fun k => by
        rw [union_comm]
        exact hHk k
      obtain ⟨hRV, hRE⟩ := hdata.residual_inter_vertexBallImage_eq_of_sides hdisk hR hfr
        hint h7 hw hwsK hweK heKt hscomp hY hX hYX hYXi hHk' hXb hYR hXR
      exact ⟨Y, Yb, hY, hYb, hRV, hRE, fun k => (hI k).2⟩
  obtain ⟨A, Ab, hA, hAb, hRV, hRE, hI⟩ := hkey
  constructor
  · rw [hRV]
    have hb : Ab = (⋃ k, tgtA ⟨(sK k, w), hwsK k⟩) ∪
        ⋃ k, R ∩ section34SplitDiskImage src f₁ (eK k) := by
      rw [hAb]
      congr 1
      exact iUnion_congr fun k => (hRE k).symm
    exact hb ▸ hA
  · intro k
    rw [hRE k, hp k, hq (k + 1) k rfl, singleton_union]
    exact hI k

end DifferentialGeometry.Topology.PiecewiseLinear
