/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLDiskChartArcSplit
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceDiskIncidence

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂} {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea}
  {f₁ : M₁ → M₂} {tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {fbl fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}

omit [FiniteDimensional ℝ Ea] in
theorem Section34FaceDiskFamily.exists_arcs_of_inter_eq_pair
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    (s : Section34SimplexIndex 𝒦 3) {B₁ B₂ : Set M₂} (hB₁ : IsClosed B₁)
    (hB₂ : IsClosed B₂) (hcover : tgtDBd s ⊆ B₁ ∪ B₂)
    (hsub : B₁ ∪ B₂ ⊆ ⋃ w, tgtV w) {p q : M₂} (hpq : p ≠ q)
    (hinter : tgtD s ∩ B₁ ∩ B₂ = {p, q}) (hne₁ : ((tgtD s ∩ B₁) \ {p, q}).Nonempty)
    (hne₂ : ((tgtD s ∩ B₂) \ {p, q}).Nonempty)
    {chart : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    (hchart : chart ∈ (plGroupoid 3).maximalAtlas M₂) (hDc : tgtD s ⊆ chart.source) :
    tgtDBd s = tgtD s ∩ B₁ ∪ tgtD s ∩ B₂ ∧
      (∃ γ₁ : ℝ → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn γ₁ (Icc 0 1) (chart '' (tgtD s ∩ B₁)) ∧
        γ₁ 0 = chart p ∧ γ₁ 1 = chart q) ∧
      ∃ γ₂ : ℝ → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn γ₂ (Icc 0 1) (chart '' (tgtD s ∩ B₂)) ∧
        γ₂ 0 = chart p ∧ γ₂ 1 = chart q := by
  obtain ⟨hD, -, hD3, -⟩ := hdisk
  have hDc' : IsClosed (tgtD s) := (hD s).isCompact.isClosed
  have hunion : tgtD s ∩ B₁ ∪ tgtD s ∩ B₂ = tgtDBd s := by
    rw [← inter_union_distrib_left]
    apply Subset.antisymm
    · rw [← hD3 s]
      exact inter_subset_inter_right _ hsub
    · exact subset_inter (hD s).boundary_subset hcover
  have hinter' : tgtD s ∩ B₁ ∩ (tgtD s ∩ B₂) = {p, q} := by
    rw [← hinter]
    ext z
    simp only [mem_inter_iff]
    tauto
  exact ⟨hunion.symm, (hD s).exists_arcs_in_chart_of_boundary_partition (hDc'.inter hB₁)
    (hDc'.inter hB₂) hunion hpq hinter' hne₁ hne₂ hchart hDc⟩

omit [FiniteDimensional ℝ Ea] in
theorem Section34FaceDiskFamily.exists_arcs_of_holes
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (tgtV)
      (tgtE) (tgtEBd)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {B₁ B₂ : Set M₂} (hB₁ : IsClosed B₁) (hB₂ : IsClosed B₂)
    (hsub : B₁ ∪ B₂ ⊆ ⋃ w, tgtV w) {H : Fin 4 → Set M₂}
    (hHE : ∀ k, ∃ e : Section34EdgeIndex 𝒦 𝒦', H k = tgtE e)
    (h12 : B₁ ∩ B₂ = ⋃ k, H k) (s : Section34SimplexIndex 𝒦 3)
    (hcov : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 →
      tgtV w ⊆ B₁ ∪ B₂)
    {i j : Fin 4} {p q : M₂} (hHi : tgtD s ∩ H i = {p}) (hHj : tgtD s ∩ H j = {q})
    (hHij : Disjoint (H i) (H j)) (hHo : ∀ k, k ≠ i → k ≠ j → tgtD s ∩ H k = ∅)
    {w₁ w₂ : Section34VertexIndex 𝒦 𝒦'} (hw₁ : Section34Incident w₁.1 s.1)
    (hw₂ : Section34Incident w₂.1 s.1) (hV₁ : tgtV w₁ ⊆ B₁)
    (hV₂ : tgtV w₂ ⊆ B₂)
    {chart : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    (hchart : chart ∈ (plGroupoid 3).maximalAtlas M₂) (hDc : tgtD s ⊆ chart.source) :
    p ≠ q ∧ tgtDBd s = tgtD s ∩ B₁ ∪ tgtD s ∩ B₂ ∧ tgtD s ∩ B₁ ∩ (tgtD s ∩ B₂) = {p, q} ∧
      (∃ γ₁ : ℝ → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn γ₁ (Icc 0 1) (chart '' (tgtD s ∩ B₁)) ∧
        γ₁ 0 = chart p ∧ γ₁ 1 = chart q) ∧
      ∃ γ₂ : ℝ → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn γ₂ (Icc 0 1) (chart '' (tgtD s ∩ B₂)) ∧
        γ₂ 0 = chart p ∧ γ₂ 1 = chart q := by
  have hpH : p ∈ H i := (hHi.symm.subset (mem_singleton p)).2
  have hqH : q ∈ H j := (hHj.symm.subset (mem_singleton q)).2
  have hpD : p ∈ tgtD s := (hHi.symm.subset (mem_singleton p)).1
  have hqD : q ∈ tgtD s := (hHj.symm.subset (mem_singleton q)).1
  have hpq : p ≠ q := fun h => Set.disjoint_left.mp hHij hpH (by rw [h]; exact hqH)
  have hinter : tgtD s ∩ B₁ ∩ B₂ = {p, q} := by
    apply Subset.antisymm
    · rintro z ⟨⟨hzD, hz1⟩, hz2⟩
      have hz12 : z ∈ B₁ ∩ B₂ := ⟨hz1, hz2⟩
      rw [h12] at hz12
      obtain ⟨k, hk⟩ := mem_iUnion.mp hz12
      by_cases hki : k = i
      · subst hki
        exact Or.inl (hHi.subset ⟨hzD, hk⟩)
      · by_cases hkj : k = j
        · subst hkj
          exact Or.inr (hHj.subset ⟨hzD, hk⟩)
        · have h0 : z ∈ tgtD s ∩ H k := ⟨hzD, hk⟩
          rw [hHo k hki hkj] at h0
          exact h0.elim
    · have hHB : ∀ k, H k ⊆ B₁ ∩ B₂ := fun k => by
        rw [h12]
        exact subset_iUnion H k
      rintro z (rfl | rfl)
      · exact ⟨⟨hpD, (hHB i hpH).1⟩, (hHB i hpH).2⟩
      · exact ⟨⟨hqD, (hHB j hqH).1⟩, (hHB j hqH).2⟩
  have hcover : tgtDBd s ⊆ B₁ ∪ B₂ := by
    obtain ⟨-, -, hD3, -, -, -, -, hD8, -⟩ := hdisk
    intro z hz
    rw [← hD3 s] at hz
    obtain ⟨w, hzw⟩ := mem_iUnion.mp hz.2
    refine hcov w ?_ hzw
    by_contra hns
    have h0 : z ∈ tgtD s ∩ tgtV w := ⟨hz.1, hzw⟩
    rw [hD8 s w hns] at h0
    exact h0
  have hne : ∀ {B : Set M₂} {w : Section34VertexIndex 𝒦 𝒦'},
      Section34Incident w.1 s.1 → tgtV w ⊆ B →
      ((tgtD s ∩ B) \ {p, q}).Nonempty := by
    intro B w hw hVB
    obtain ⟨z, hzA, hzE⟩ := hdisk.exists_mem_faceArc_notMem_splitDisk ⟨(s, w), hw⟩
    have hzDV := (hdisk.faceDisk_inter_vertexBall_eq ⟨(s, w), hw⟩).symm.subset hzA
    refine ⟨z, ⟨hzDV.1, hVB hzDV.2⟩, ?_⟩
    rintro (rfl | rfl)
    · obtain ⟨e, he⟩ := hHE i
      exact hzE e (by rw [← he]; exact hpH)
    · obtain ⟨e, he⟩ := hHE j
      exact hzE e (by rw [← he]; exact hqH)
  obtain ⟨hDb, hγ₁, hγ₂⟩ := hdisk.exists_arcs_of_inter_eq_pair s hB₁ hB₂ hcover hsub hpq hinter
    (hne hw₁ hV₁) (hne hw₂ hV₂) hchart hDc
  refine ⟨hpq, hDb, ?_, hγ₁, hγ₂⟩
  rw [← hinter]
  ext z
  simp only [mem_inter_iff]
  tauto

theorem Section34FaceDiskFamily.exists_runs_of_face
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd)
    (hdisk : Section34FaceDiskFamily 𝒦 𝒦' (tgtV)
      (tgtE) (tgtEBd)
      fblBd tgtD tgtDBd tgtA tgtABd tgtP)
    {B₁ B₂ : Set M₂} (hB₁ : IsClosed B₁) (hB₂ : IsClosed B₂)
    (hsub : B₁ ∪ B₂ ⊆ ⋃ w, tgtV w)
    {eH : Fin 4 → Section34EdgeIndex 𝒦 𝒦'}
    (h12 : B₁ ∩ B₂ = ⋃ k, tgtE (eH k))
    (s : Section34SimplexIndex 𝒦 3)
    (hcov : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 →
      tgtV w ⊆ B₁ ∪ B₂)
    {i j : Fin 4} (hij : eH i ≠ eH j) (hsi : Section34Incident (eH i).1 s.1)
    (hsj : Section34Incident (eH j).1 s.1)
    (hso : ∀ k, k ≠ i → k ≠ j → ¬ Section34Incident (eH k).1 s.1)
    {w₁ w₂ : Section34VertexIndex 𝒦 𝒦'} (hw₁ : Section34Incident w₁.1 s.1)
    (hw₂ : Section34Incident w₂.1 s.1) (hV₁ : tgtV w₁ ⊆ B₁)
    (hV₂ : tgtV w₂ ⊆ B₂)
    {chart : OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
    (hchart : chart ∈ (plGroupoid 3).maximalAtlas M₂) (hDc : tgtD s ⊆ chart.source) :
    ∃ p q : M₂, p ∈ tgtEBd (eH i) ∧
      q ∈ tgtEBd (eH j) ∧
      tgtD s ∩ tgtE (eH i) = {p} ∧
      tgtD s ∩ tgtE (eH j) = {q} ∧
      (∀ k, k ≠ i → k ≠ j → tgtD s ∩ tgtE (eH k) = ∅) ∧
      tgtDBd s = tgtD s ∩ B₁ ∪ tgtD s ∩ B₂ ∧ tgtD s ∩ B₁ ∩ (tgtD s ∩ B₂) = {p, q} ∧
      (∃ γ₁ : ℝ → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn γ₁ (Icc 0 1) (chart '' (tgtD s ∩ B₁)) ∧
        γ₁ 0 = chart p ∧ γ₁ 1 = chart q) ∧
      ∃ γ₂ : ℝ → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn γ₂ (Icc 0 1) (chart '' (tgtD s ∩ B₂)) ∧
        γ₂ 0 = chart p ∧ γ₂ 1 = chart q := by
  obtain ⟨p, hp, hpb⟩ := hdisk.exists_faceDisk_inter_splitDisk_eq_singleton hdata s _ hsi
  obtain ⟨q, hq, hqb⟩ := hdisk.exists_faceDisk_inter_splitDisk_eq_singleton hdata s _ hsj
  have hso' : ∀ k, k ≠ i → k ≠ j →
      tgtD s ∩ tgtE (eH k) = ∅ := fun k hki hkj =>
    hdisk.faceDisk_inter_splitDisk_eq_empty hdata (hso k hki hkj)
  have hdisj : Disjoint (tgtE (eH i)) (tgtE (eH j)) := by
    obtain ⟨hcut, -, hgraph, -, -, -, hE, -⟩ := hdata
    rw [hE (eH i), hE (eH j)]
    exact hcut.disjoint_splitDiskImage hgraph.2.2.1.injOn hij
  obtain ⟨-, hDb, hinter, hγ₁, hγ₂⟩ := hdisk.exists_arcs_of_holes hB₁ hB₂ hsub
    (fun k => ⟨eH k, rfl⟩) h12 s hcov hp hq hdisj hso' hw₁ hw₂
    hV₁ hV₂ hchart hDc
  exact ⟨p, q, hpb, hqb, hp, hq, hso', hDb, hinter, hγ₁, hγ₂⟩

end DifferentialGeometry.Topology.PiecewiseLinear
