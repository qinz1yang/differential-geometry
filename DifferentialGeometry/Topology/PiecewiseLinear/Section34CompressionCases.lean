/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionTools
import DifferentialGeometry.Topology.PiecewiseLinear.TetrahedronStarComplement

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Dichotomy

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]

theorem subset_interior_or_disjoint_sdiff_of_isPLCellOn
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 3))}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M) {F Fb Dj Jd : Set M} (hF : IsPLCellOn 3 F Fb)
    (hD : IsPLCellOn 2 Dj Jd) (hFc : F ⊆ c.source) (hDc : Dj ⊆ c.source)
    (hDF : Dj ∩ Fb ⊆ Jd) : Dj \ Jd ⊆ interior F ∨ Disjoint (Dj \ Jd) F := by
  obtain ⟨-, hFfr⟩ := hF.isPLBall_image_chart hc hFc
  obtain ⟨q, hq, hqJ⟩ := hD.exists_isPLHomeomorphOn_image_chart hc hDc
  have hFcomp : IsCompact F := hF.isCompact
  have hfrF : frontier F = Fb := by
    have h1 : c '' frontier F = c '' Fb := by
      rw [c.image_frontier_of_isCompact hFcomp hFc, hFfr]
    have hfrc : frontier F ⊆ c.source := hFcomp.isClosed.frontier_subset.trans hFc
    have hFbc : Fb ⊆ c.source := hF.boundary_subset.trans hFc
    exact (c.injOn.image_eq_image_iff hfrc hFbc).mp h1
  have hJD : Jd ⊆ Dj := hD.boundary_subset
  have hopen : c '' (Dj \ Jd) = q '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) \ stdSimplexBoundary 2) := by
    rw [(c.injOn.mono hDc).image_sdiff_subset hJD, ← hq.image_eq, hqJ,
      hq.bijOn.injOn.image_sdiff_subset (fun x hx => hx.1)]
  have hconv : Convex ℝ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) \ stdSimplexBoundary 2) := by
    intro x hx y hy a b ha hb hab
    refine ⟨(Convexity.StdSimplex.convex_coordinateSet ℝ (Fin 3)) hx.1 hy.1 ha hb hab, ?_⟩
    rintro ⟨-, i, hi⟩
    have hxi : 0 < x i := lt_of_le_of_ne (hx.1.1 i) fun h => hx.2 ⟨hx.1, i, h.symm⟩
    have hyi : 0 < y i := lt_of_le_of_ne (hy.1.1 i) fun h => hy.2 ⟨hy.1, i, h.symm⟩
    have hsum : (a • x + b • y) i = a * x i + b * y i := by simp
    rw [hsum] at hi
    rcases eq_or_lt_of_le ha with rfl | ha'
    · simp only [zero_add] at hab
      subst hab
      nlinarith
    · nlinarith [mul_pos ha' hxi, mul_nonneg hb hyi.le]
  have hpcq : IsPreconnected (q '' (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) \ stdSimplexBoundary 2)) :=
    hconv.isPreconnected.image q (hq.isPiecewiseAffineOn.continuousOn.mono fun x hx => hx.1)
  have hDJc : Dj \ Jd ⊆ c.source := sdiff_subset.trans hDc
  have hpc : IsPreconnected (Dj \ Jd) := by
    have ht : c '' (Dj \ Jd) ⊆ c.target := by
      rintro _ ⟨x, hx, rfl⟩
      exact c.map_source (hDJc hx)
    have h1 := hpcq.image c.symm (hopen ▸ c.continuousOn_symm.mono ht)
    rw [← hopen] at h1
    convert h1 using 1
    exact (c.symm_image_image_of_subset_source hDJc).symm
  have hfr : Disjoint (Dj \ Jd) (frontier F) := by
    rw [hfrF]
    exact Set.disjoint_left.mpr fun x hx hxb => hx.2 (hDF ⟨hx.1, hxb⟩)
  by_cases hne : (Dj \ Jd ∩ F).Nonempty
  · left
    have hsub := IsPreconnected.subset_of_disjoint_frontier hpc hne hfr
    intro x hx
    rw [← hFcomp.isClosed.closure_eq] at hsub
    exact (mem_interior_iff_notMem_frontier (hFcomp.isClosed.closure_eq ▸ hsub hx)).mpr
      (Set.disjoint_left.mp hfr hx)
  · right
    exact Set.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne)

end Dichotomy

section Escape

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] {U : Set M₁} {h : M₁ → M₂} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}

theorem exists_tetra_section34Incident_not_incident [FiniteDimensional ℝ Ea]
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (s : Section34SimplexIndex 𝒦 3)
    {w : Section34VertexIndex 𝒦 𝒦'} (hw : ¬ Section34Incident w.1 s.1) :
    ∃ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 ∧
      ¬ Section34Incident w.1 t.1 := by
  classical
  obtain ⟨hK, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcof⟩ := hcut
  obtain ⟨t₁, hst₁⟩ := hcof s
  have hsub : s.1 ⊆ t₁.1 := by
    intro v hv
    have hvs : ({v} : Finset Ea) ∈ 𝒦.complex.faces :=
      𝒦.complex.down_closed s.2.1 (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)
    exact mem_of_mem_convexHull_of_singleton_mem 𝒦.complex hvs t₁.2.1
      (hst₁ (Finset.mem_coe.mpr hv))
  obtain ⟨d, hdt, hds⟩ : ∃ d ∈ t₁.1, d ∉ s.1 := by
    by_contra hcon
    push Not at hcon
    have hle := Finset.card_le_card (show t₁.1 ⊆ s.1 from hcon)
    rw [t₁.2.2, s.2.2] at hle
    omega
  have ht₁eq : t₁.1 = insert d s.1 := by
    refine (Finset.eq_of_subset_of_card_le (Finset.insert_subset hdt hsub) ?_).symm
    rw [Finset.card_insert_of_notMem hds, t₁.2.2, s.2.2]
  have hins : insert d s.1 ∈ 𝒦.complex.faces := ht₁eq ▸ t₁.2.1
  obtain ⟨z, hzs, hzd, hz⟩ := 𝒦.exists_insert_mem_faces_ne hK s.2.1 s.2.2 hds hins
  have hzcard : (insert z s.1).card = 4 := by
    rw [Finset.card_insert_of_notMem hzs, s.2.2]
  have hst₂ : Section34Incident s.1 (insert z s.1) := fun x hx =>
    subset_convexHull ℝ _ (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx)))
  by_cases hw₁ : Section34Incident w.1 t₁.1
  · refine ⟨⟨insert z s.1, hz, hzcard⟩, hst₂, fun hw₂ => hw fun x hx => ?_⟩
    have hmem := 𝒦.complex.inter_subset_convexHull t₁.2.1 hz ⟨hw₁ hx, hw₂ hx⟩
    rw [ht₁eq] at hmem
    refine convexHull_mono ?_ hmem
    rintro y ⟨hy1, hy2⟩
    simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe] at hy1 hy2
    rcases hy1 with rfl | hy1
    · rcases hy2 with rfl | hy2
      · exact absurd rfl hzd
      · exact hy2
    · exact hy1
  · exact ⟨t₁, hst₁, hw₁⟩

theorem Section34Exterior.notMem_of_frontier_subset
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂}
    {fbl : Section34SimplexIndex 𝒦 3 → Set M₂} (hext : Section34Exterior 𝒦 𝒦' h H tgtV fbl)
    {t : Section34SimplexIndex 𝒦 4} {w : Section34VertexIndex 𝒦 𝒦'}
    (hw : ¬ Section34Incident w.1 t.1) {y : M₂} (hy : y ∈ h '' simplexBody 𝒦' w.1)
    (hyH : y ∈ H t.1) {K : Set M₂} (hK : frontier K ⊆ section34TetraObstacle tgtV fbl t)
    (hKH : Disjoint K (frontier (H t.1))) : y ∉ K := by
  obtain ⟨-, -, h3⟩ := hext
  obtain ⟨hyo, hne⟩ := h3 t w hw y hy hyH
  intro hyK
  have hpc : IsPreconnected
      (connectedComponentIn (H t.1 \ section34TetraObstacle tgtV fbl t) y) :=
    isPreconnected_connectedComponentIn
  have hCK := IsPreconnected.subset_of_disjoint_frontier hpc
    ⟨y, mem_connectedComponentIn ⟨hyH, hyo⟩, hyK⟩
    (Set.disjoint_left.mpr fun z hz hzf => (connectedComponentIn_subset _ y hz).2 (hK hzf))
  obtain ⟨z, hzC, hzf⟩ := hne
  exact Set.disjoint_left.mp hKH (hCK hzC) hzf

end Escape

end DifferentialGeometry.Topology.PiecewiseLinear
