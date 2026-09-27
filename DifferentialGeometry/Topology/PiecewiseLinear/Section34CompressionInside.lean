/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTraceCircles
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceHomology
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionTools
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceTorusCycle

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Compression

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η ψ : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

theorem exists_section34Compression_of_subset (hh : Topology.IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
      (section34SplitDiskImage srcBd f₁) fbl fblBd)
    (s : Section34SimplexIndex 𝒦 3) {w : Section34VertexIndex 𝒦 𝒦'} {Dj Jd : Set M₂}
    (hDcell : IsPLCellOn 2 Dj Jd) (hDw : Dj ⊆ section34VertexBallImage srcBd f₁ w)
    (hDJ : Dj ∩ fblBd s = Jd)
    (hDE : ∀ e : Section34EdgeIndex 𝒦 𝒦', Disjoint Dj (section34SplitDiskImage src f₁ e))
    (hDs : Dj ⊆ fbl s) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34TraceCount (section34VertexBallImage src f₁) fblBd' s + 1 ≤
        section34TraceCount (section34VertexBallImage src f₁) fblBd s ∧
      section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd' s ≤
        section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd s := by
  classical
  obtain ⟨hfcell, hfrim, hfV, -, hf5, -, hf7, -, -, hext⟩ := id hinv
  obtain ⟨-, hsubdiv, -, hcell, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hends, -, -⟩ := id hcut
  obtain ⟨-, -, hf₁, -, -, -, -, -, hrimT, -, -, -, -, -⟩ := id hgraph
  obtain ⟨c, hc, hfsc, hTc, hTcomp, O₀, hO₀, hfO₀, hSgO₀⟩ :=
    exists_chart_section34FaceBall hh hcut hctrl hgraph hext s (hfV s)
  set T := section34FaceTorus (section34VertexBallImage src f₁) s
  set Sg := frontier (⋃ w', section34VertexBallImage src f₁ w')
  have hNV : ∀ v : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall v) ⊆ section34CutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (Section34Label.vertexBall v)) v
  have hVT : ∀ w' : Section34VertexIndex 𝒦 𝒦', Section34Incident w'.1 s.1 →
      section34VertexBallImage src f₁ w' ⊆ T := fun w' hw z hz =>
    mem_iUnion₂.mpr ⟨⟨(s, w'), hw⟩, rfl, hz⟩
  have hTinc : ∀ z ∈ T, ∃ w' : Section34VertexIndex 𝒦 𝒦', Section34Incident w'.1 s.1 ∧
      z ∈ section34VertexBallImage src f₁ w' := by
    intro z hz
    obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
    refine ⟨a.1.2, ?_, hza⟩
    rw [← ha]
    exact a.2
  have hVc : ∀ w' : Section34VertexIndex 𝒦 𝒦', Section34Incident w'.1 s.1 →
      section34VertexBallImage src f₁ w' ⊆ c.source := fun w' hw => (hVT w' hw).trans hTc
  have hfbs : fblBd s ⊆ fbl s := (hfcell s).boundary_subset
  have hVcell : ∀ w' : Section34VertexIndex 𝒦 𝒦',
      IsPLCellOn 3 (section34VertexBallImage src f₁ w') (section34VertexBallImage srcBd f₁ w') :=
    fun w' => (hcell (.vertexBall w')).image
      (hf₁.mono_of_isPLCellOn (hcell (.vertexBall w')) (hNV w'))
  have hDN : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      src (.splitDisk e) ⊆ section34CutNeighborhood src := by
    intro e
    obtain ⟨w', _, -, -, he⟩ := hends e
    rw [he]
    exact inter_subset_left.trans (hNV w')
  have hwinc : Section34Incident w.1 s.1 := by
    by_contra hn
    obtain ⟨z, hz⟩ := hDcell.nonempty
    have hmem : z ∈ fbl s ∩ section34VertexBallImage src f₁ w :=
      ⟨hDs hz, image_mono (hcell (.vertexBall w)).boundary_subset (hDw hz)⟩
    rw [hfV s w hn] at hmem
    exact hmem
  have hDjV : ∀ w' : Section34VertexIndex 𝒦 𝒦', w' ≠ w →
      Disjoint Dj (section34VertexBallImage src f₁ w') := by
    intro w' hw'
    refine Set.disjoint_left.mpr fun z hz hz' => ?_
    obtain ⟨a, ha, haz⟩ := image_mono (hcell (.vertexBall w)).boundary_subset (hDw hz)
    obtain ⟨b, hb, hbz⟩ := hz'
    have hEq : b = a := hf₁.injOn (hNV w' hb) (hNV w ha) (hbz.trans haz.symm)
    rw [hEq] at hb
    obtain ⟨e, he⟩ := exists_splitDisk_src_eq_inter_vertexBall hcut hw'.symm ⟨a, ha, hb⟩
    refine Set.disjoint_left.mp (hDE e) hz ⟨a, ?_, haz⟩
    rw [he]
    exact ⟨ha, hb⟩
  have hIfin := finite_setOf_section34Incident_graphIndex hsubdiv (graphSkeletonSpace 𝒦) 1 s.2.1
  have hEfin := finite_setOf_section34Incident_graphIndex hsubdiv (graphSkeletonSpace 𝒦) 2 s.2.1
  have hcT : IsCompact (c '' T) := hTcomp.image_of_continuousOn (c.continuousOn.mono hTc)
  have hTcl : IsClosed (c '' T) := hcT.isClosed
  set Θ := frontier (c '' T)
  have hΘeq : c '' frontier T = Θ := c.image_frontier_of_isCompact hTcomp hTc
  have hfrTc : frontier T ⊆ c.source := hTcomp.isClosed.frontier_subset.trans hTc
  have hΘt : Θ ⊆ c.target := by
    rw [← hΘeq]
    rintro _ ⟨y, hy, rfl⟩
    exact c.map_source (hfrTc hy)
  have hΘtor : IsPLTorus Θ := by
    rw [← hΘeq]
    exact isPLTorus_image_frontier_section34FaceTorus hcut (hgraph.2.2.1) s hc hTc
  have hTsolid := isCombinatorialSolidTorus_image_section34FaceTorus hcut (hgraph.2.2.1) s hc hTc
  have hmemT : ∀ y ∈ c.source, (y ∈ frontier T ↔ c y ∈ Θ) := by
    intro y hy
    rw [← hΘeq]
    constructor
    · exact fun h1 => mem_image_of_mem c h1
    · rintro ⟨y', hy', hyy⟩
      rwa [← c.injOn (hfrTc hy') hy hyy]
  obtain ⟨hPb, hPfr⟩ := (hfcell s).isPLBall_image_chart hc hfsc
  have hmemP : ∀ y ∈ c.source, (y ∈ fblBd s ↔ c y ∈ frontier (c '' fbl s)) := by
    intro y hy
    rw [← hPfr]
    constructor
    · exact fun h1 => mem_image_of_mem c h1
    · rintro ⟨y', hy', hyy⟩
      rwa [← c.injOn (hfsc (hfbs hy')) hy hyy]
  have hmemSg : ∀ y ∈ fbl s, (y ∈ Sg ↔ c y ∈ Θ) := by
    intro y hy
    have hyO := hfO₀ hy
    rw [← hmemT y (hfsc hy)]
    constructor
    · intro h1
      have h2 : y ∈ Sg ∩ O₀ := ⟨h1, hyO⟩
      rw [hSgO₀] at h2
      exact h2.1
    · intro h1
      have h2 : y ∈ frontier T ∩ O₀ := ⟨h1, hyO⟩
      rw [← hSgO₀] at h2
      exact h2.1
  have hcrossΘ : ∀ y ∈ fblBd s ∩ frontier T,
      HasPLCrossingAt (frontier (c '' fbl s)) Θ (c y) := by
    rintro y ⟨hyb, hyT⟩
    have hyO₀ : y ∈ O₀ := hfO₀ (hfbs hyb)
    have hy : y ∈ c.source := hfsc (hfbs hyb)
    have hySg : y ∈ Sg := (hmemSg y (hfbs hyb)).mpr ((hmemT y hy).mp hyT)
    obtain ⟨c', hc', hyc', hcr⟩ := hf5 s y ⟨hyb, hySg⟩
    have hcr' := hcr.image_chart_of_mem_maximalAtlas hc hc' hy hyc'
    refine hcr'.congr ?_ ?_
    · rw [inter_eq_left.mpr (hfbs.trans hfsc), hPfr]
      exact Filter.Eventually.of_forall fun _ => Iff.rfl
    · filter_upwards [eventually_mem_image_inter_source_iff hO₀ hSgO₀ hyO₀ hy] with z hz
      rw [hz, inter_eq_left.mpr hfrTc, hΘeq]
  have hDjc : Dj ⊆ c.source := hDs.trans hfsc
  obtain ⟨q, hq, hqJ⟩ := hDcell.exists_isPLHomeomorphOn_image_chart hc hDjc
  have hJdb : Jd ⊆ fblBd s := by
    rw [← hDJ]
    exact inter_subset_right
  have hJdD : Jd ⊆ Dj := by
    rw [← hDJ]
    exact inter_subset_left
  have htrace : c '' Dj ∩ frontier (c '' fbl s) = q '' stdSimplexBoundary 2 := by
    rw [← hPfr, ← c.injOn.image_inter hDjc (hfbs.trans hfsc), hDJ, hqJ]
  obtain ⟨hVwb, hVwfr⟩ := (hVcell w).isPLBall_image_chart hc (hVc w hwinc)
  obtain ⟨Oo, hOo, hDO, hΘO⟩ : ∃ Oo : Set (EuclideanSpace ℝ (Fin 3)), IsOpen Oo ∧
      c '' Dj ⊆ Oo ∧ Oo ∩ Θ = Oo ∩ frontier (c '' section34VertexBallImage src f₁ w) := by
    have hcl : IsClosed (⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
        Section34Incident w'.1 s.1 ∧ w' ≠ w}, c '' section34VertexBallImage src f₁ w') :=
      (hIfin.subset fun w' hw' => hw'.1).isClosed_biUnion fun w' hw' =>
        ((hVcell w').isCompact.image_of_continuousOn
          (c.continuousOn.mono (hVc w' hw'.1))).isClosed
    have hcTO : c '' T ∩ (⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
        Section34Incident w'.1 s.1 ∧ w' ≠ w}, c '' section34VertexBallImage src f₁ w')ᶜ =
        c '' section34VertexBallImage src f₁ w ∩ (⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
          Section34Incident w'.1 s.1 ∧ w' ≠ w}, c '' section34VertexBallImage src f₁ w')ᶜ := by
      apply Subset.antisymm
      · rintro _ ⟨⟨z, hz, rfl⟩, hzO⟩
        obtain ⟨w', hw', hzw'⟩ := hTinc z hz
        by_cases hww : w' = w
        · subst hww
          exact ⟨⟨z, hzw', rfl⟩, hzO⟩
        · exact (hzO (mem_iUnion₂.mpr ⟨w', ⟨hw', hww⟩, ⟨z, hzw', rfl⟩⟩)).elim
      · exact inter_subset_inter_left _ (image_mono (hVT w hwinc))
    refine ⟨_, hcl.isOpen_compl, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩ hzU
      obtain ⟨w', ⟨hw', hww⟩, ⟨z', hz', hzz⟩⟩ := mem_iUnion₂.mp hzU
      have hzz' := c.injOn (hVc w' hw' hz') (hDjc hz) hzz
      rw [hzz'] at hz'
      exact Set.disjoint_left.mp (hDjV w' hww) hz hz'
    · have h1 := frontier_inter_open_inter (s := c '' T) hcl.isOpen_compl
      have h2 := frontier_inter_open_inter (s := c '' section34VertexBallImage src f₁ w)
        hcl.isOpen_compl
      rw [hcTO] at h1
      change _ ∩ frontier (c '' T) = _
      rw [inter_comm _ (frontier (c '' T)), inter_comm _ (frontier _), ← h1, h2]
  have hDjT : Dj ⊆ frontier T := by
    intro z hz
    have hzc : c z ∈ Oo ∩ frontier (c '' section34VertexBallImage src f₁ w) :=
      ⟨hDO ⟨z, hz, rfl⟩, hVwfr.subset ⟨z, hDw hz, rfl⟩⟩
    rw [← hΘO] at hzc
    exact (hmemT z (hDjc hz)).mpr hzc.2
  have hDjSg : Dj ⊆ Sg := fun z hz =>
    (hmemSg z (hDs hz)).mpr ((hmemT z (hDjc hz)).mp (hDjT hz))
  have hcrossJ : ∀ x ∈ q '' stdSimplexBoundary 2,
      HasPLCrossingAt (frontier (c '' fbl s)) Θ x := by
    intro x hx
    rw [← hqJ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hcrossΘ y ⟨hJdb hy, hDjT (hJdD hy)⟩
  have hEsc : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
      section34SplitDiskImage src f₁ e ⊆ c.source := by
    intro e he
    obtain ⟨u, u', -, hew, hDu⟩ := hends e
    have hue : ((u.1 : Finset Ea) : Set Ea) ⊆ (e.1 : Set Ea) := by
      rw [hew]
      exact subset_union_left
    change f₁ '' src (.splitDisk e) ⊆ c.source
    rw [hDu]
    exact (image_mono inter_subset_left).trans (hVc u (hue.trans he))
  have hEcc : IsClosed (⋃ e ∈ {e : Section34EdgeIndex 𝒦 𝒦' | Section34Incident e.1 s.1},
      c '' section34SplitDiskImage src f₁ e) := hEfin.isClosed_biUnion fun e he =>
    (((hcell (.splitDisk e)).image (hf₁.mono_of_isPLCellOn (hcell (.splitDisk e))
      (hDN e))).isCompact.image_of_continuousOn (c.continuousOn.mono (hEsc e he))).isClosed
  have hDEc : Disjoint (c '' Dj) (⋃ e ∈ {e : Section34EdgeIndex 𝒦 𝒦' |
      Section34Incident e.1 s.1}, c '' section34SplitDiskImage src f₁ e) := by
    refine Set.disjoint_left.mpr fun x hx hxE => ?_
    obtain ⟨e, he, z, hz, hzx⟩ := mem_iUnion₂.mp hxE
    obtain ⟨y, hy, rfl⟩ := hx
    have hzy := c.injOn (hEsc e he hz) (hDjc hy) hzx
    rw [hzy] at hz
    exact Set.disjoint_left.mp (hDE e) hy hz
  set R : Set Ea := ⋃ u ∈ s.1, convexHull ℝ ((s.1.erase u : Finset Ea) : Set Ea)
  have hRsph : IsPLSphere 1 R := isPLSphere_biUnion_erase s.1 (𝒦.complex.indep s.2.1) s.2.2
  have hR𝒦 : R ⊆ 𝒦.complex.space :=
    (iUnion₂_subset fun u _ =>
      convexHull_mono (Finset.coe_subset.mpr (Finset.erase_subset u s.1))).trans
      (𝒦.complex.convexHull_subset_space s.2.1)
  have hrimeq : simplexRim 𝒦 s.1 = 𝒦.map '' R := by
    apply Subset.antisymm
    · intro x hx
      obtain ⟨τ, hτ, a, ha, rfl⟩ := mem_iUnion₂.mp hx
      obtain ⟨u, hus, huτ⟩ := Finset.exists_of_ssubset hτ
      refine ⟨a, mem_iUnion₂.mpr ⟨u, hus, convexHull_mono ?_ ha⟩, rfl⟩
      intro z hz
      rw [Finset.coe_erase]
      exact ⟨Finset.coe_subset.mpr hτ.subset hz,
        fun hzu => huτ ((mem_singleton_iff.mp hzu) ▸ hz)⟩
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨u, hu, hau⟩ := mem_iUnion₂.mp ha
      exact mem_iUnion₂.mpr ⟨s.1.erase u, Finset.erase_ssubset hu, a, hau, rfl⟩
  have hhU : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hrimU : 𝒦.map '' R ⊆ U := by
    rintro _ ⟨a, ha, rfl⟩
    exact 𝒦.bijOn.mapsTo (hR𝒦 ha)
  have hrimc : h '' simplexRim 𝒦 s.1 ⊆ c.source := (hfrim s).trans (interior_subset.trans hfsc)
  have hKc : IsCompact (c '' (h '' simplexRim 𝒦 s.1)) := by
    have h1 : IsCompact (𝒦.map '' R) :=
      hRsph.isPolyhedron.isCompact.image_of_continuousOn (𝒦.continuousOn.mono hR𝒦)
    have h2 := h1.image_of_continuousOn (hhU.mono hrimU)
    rw [← hrimeq] at h2
    exact h2.image_of_continuousOn (c.continuousOn.mono hrimc)
  have hKpc : IsPreconnected (c '' (h '' simplexRim 𝒦 s.1)) := by
    have h1 : IsPreconnected (𝒦.map '' R) :=
      hRsph.isConnected.isPreconnected.image _ (𝒦.continuousOn.mono hR𝒦)
    have h2 := h1.image h (hhU.mono hrimU)
    rw [← hrimeq] at h2
    exact h2.image c (c.continuousOn.mono hrimc)
  have hKP : c '' (h '' simplexRim 𝒦 s.1) ⊆ interior (c '' fbl s) :=
    (image_mono (hfrim s)).trans (interior_maximal (image_mono interior_subset)
      (c.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hfsc)))
  have hKD : Disjoint (c '' (h '' simplexRim 𝒦 s.1)) (c '' Dj) := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨y, hy, rfl⟩ ⟨z, hz, hzy⟩
    have hzy' := c.injOn (hDjc hz) (hrimc hy) hzy
    rw [hzy'] at hz
    exact (hDjT hz).2 (hrimT s hy)
  obtain ⟨P', Oc, hP'b, hP'P, hKP', hP'D, hOc, hfrO, hk2, hk4, hk3⟩ :=
    hPb.exists_compression_trace hq (image_mono hDs) htrace hVwb.isPLSphere_frontier
      ((image_mono hDw).trans hVwfr.subset) hOo hDO hΘO hcrossJ hEcc hDEc hKc hKpc hKP hKD
  have hPt : c '' fbl s ⊆ c.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.map_source (hfsc hy)
  have hP't : P' ⊆ c.target := hP'P.trans hPt
  have hP'poly : IsPolyhedron P' := hP'b.isPolyhedron
  have hP'c : IsClosed P' := hP'poly.isClosed
  have hfrP'P' : frontier P' ⊆ P' := hP'c.frontier_subset
  obtain ⟨r, hr⟩ := id hP'b
  have hfr : r '' stdSimplexBoundary 3 = frontier P' :=
    IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hr
  have hFcell : IsPLCellOn 3 (c.symm '' P') (c.symm '' frontier P') :=
    ⟨P', r, c.symm, hr, isPLHomeomorphInto_symm_of_mem_maximalAtlas hc hP'poly hP't, rfl,
      by rw [hfr]⟩
  have hFs : c.symm '' P' ⊆ fbl s := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hP'P hx
    rw [c.left_inv (hfsc hz)]
    exact hz
  have hFc : c.symm '' P' ⊆ c.source := hFs.trans hfsc
  have hFbF : c.symm '' frontier P' ⊆ c.symm '' P' := image_mono hfrP'P'
  have hmemF : ∀ y ∈ c.source, (y ∈ c.symm '' P' ↔ c y ∈ P') := by
    intro y hy
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [c.right_inv (hP't hx)]
      exact hx
    · exact fun hy' => ⟨c y, hy', c.left_inv hy⟩
  have hmemFb : ∀ y ∈ c.source, (y ∈ c.symm '' frontier P' ↔ c y ∈ frontier P') := by
    intro y hy
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [c.right_inv (hP't (hfrP'P' hx))]
      exact hx
    · exact fun hy' => ⟨c y, hy', c.left_inv hy⟩
  have hFrim : h '' simplexRim 𝒦 s.1 ⊆ interior (c.symm '' P') := by
    intro y hy
    refine interior_maximal (image_mono interior_subset)
      (c.isOpen_image_symm_of_subset_target isOpen_interior (interior_subset.trans hP't)) ?_
    exact ⟨c y, hKP' (mem_image_of_mem c hy), c.left_inv (hrimc hy)⟩
  have hOM : IsOpen (c.source ∩ c ⁻¹' Oc) := c.isOpen_inter_preimage hOc
  have hFbO : c.symm '' frontier P' ∩ (c.source ∩ c ⁻¹' Oc) =
      fblBd s ∩ (c.source ∩ c ⁻¹' Oc) := by
    ext y
    constructor
    · rintro ⟨hy, hyO⟩
      refine ⟨(hmemP y hyO.1).mpr ?_, hyO⟩
      have h1 : c y ∈ frontier P' ∩ Oc := ⟨(hmemFb y hyO.1).mp hy, hyO.2⟩
      rw [hfrO] at h1
      exact h1.1
    · rintro ⟨hy, hyO⟩
      refine ⟨(hmemFb y hyO.1).mpr ?_, hyO⟩
      have h1 : c y ∈ frontier (c '' fbl s) ∩ Oc := ⟨(hmemP y hyO.1).mp hy, hyO.2⟩
      rw [← hfrO] at h1
      exact h1.1
  have hZO : c.symm '' frontier P' ∩ Sg ⊆ c.source ∩ c ⁻¹' Oc := by
    rintro y ⟨hy, hySg⟩
    have hyc := hFc (hFbF hy)
    exact ⟨hyc, hk2 ⟨(hmemFb y hyc).mp hy, (hmemSg y (hFs (hFbF hy))).mp hySg⟩⟩
  have hEO : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      c.symm '' frontier P' ∩ section34SplitDiskImage srcBd f₁ e ⊆ c.source ∩ c ⁻¹' Oc := by
    rintro e y ⟨hy, hye⟩
    have hyc := hFc (hFbF hy)
    obtain ⟨u, u', -, hew, hDu⟩ := hends e
    obtain ⟨a, ha, hay⟩ := image_mono (hcell (.splitDisk e)).boundary_subset hye
    rw [hDu] at ha
    have hinc1 : ∀ v : Section34VertexIndex 𝒦 𝒦', a ∈ src (.vertexBall v) →
        Section34Incident v.1 s.1 := by
      intro v hv
      by_contra hn
      have hmem : y ∈ fbl s ∩ section34VertexBallImage src f₁ v :=
        ⟨hFs (hFbF hy), a, hv, hay⟩
      rw [hfV s v hn] at hmem
      exact hmem
    have he : Section34Incident e.1 s.1 := by
      change ((e.1 : Finset Ea) : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
      rw [hew]
      exact union_subset (hinc1 u ha.1) (hinc1 u' ha.2)
    exact ⟨hyc, hk4 ⟨(hmemFb y hyc).mp hy, mem_iUnion₂.mpr ⟨e, he, y,
      image_mono (hcell (.splitDisk e)).boundary_subset hye, rfl⟩⟩⟩
  have hZF : c.symm '' frontier P' ∩ Sg = fblBd s ∩ Sg ∩ c.symm '' P' := by
    ext y
    constructor
    · intro hy
      have h1 : y ∈ c.symm '' frontier P' ∩ (c.source ∩ c ⁻¹' Oc) := ⟨hy.1, hZO hy⟩
      rw [hFbO] at h1
      exact ⟨⟨h1.1, hy.2⟩, hFbF hy.1⟩
    · rintro ⟨⟨hy, hySg⟩, hyF⟩
      have hyc := hFc hyF
      have hx : c y ∈ frontier (c '' fbl s) ∩ Θ ∩ P' :=
        ⟨⟨(hmemP y hyc).mp hy, (hmemSg y (hfbs hy)).mp hySg⟩, (hmemF y hyc).mp hyF⟩
      rw [← hk3] at hx
      exact ⟨(hmemFb y hyc).mpr hx.1, hySg⟩
  obtain ⟨x₀, hx₀⟩ : (q '' stdSimplexBoundary 2).Nonempty :=
    (nonempty_stdSimplexBoundary_of_pos (by norm_num)).image q
  rw [← hqJ] at hx₀
  obtain ⟨y₀, hy₀J, -⟩ := hx₀
  have hy₀F : y₀ ∉ c.symm '' P' := fun hy =>
    Set.disjoint_left.mp hP'D ((hmemF y₀ (hFc hy)).mp hy) ⟨y₀, hJdD hy₀J, rfl⟩
  obtain ⟨h5, h6, h8, h9, hcount, hpcount⟩ := section34FaceBall_fields_of_inter_eq hinv hOM
    hFcell.isCompact.isClosed hFbO hZO hEO hZF ⟨hJdb hy₀J, hDjSg (hJdD hy₀J)⟩ hy₀F
  have hZc : frontier (c '' fbl s) ∩ Θ = c '' (fblBd s ∩ frontier T) := by
    rw [c.injOn.image_inter (hfbs.trans hfsc) hfrTc, hPfr, hΘeq]
  have hcTreg : ∀ x ∈ Θ, x ∈ closure (interior (c '' T)) := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ : x ∈ c '' T := hTcl.frontier_subset hx
    obtain ⟨w', hw', hzw'⟩ := hTinc z hz
    obtain ⟨hb', -⟩ := (hVcell w').isPLBall_image_chart hc (hVc w' hw')
    have hcl := hb'.closure_interior_of_finrank (by simp)
    have hzin : c z ∈ closure (interior (c '' section34VertexBallImage src f₁ w')) := by
      rw [hcl]
      exact ⟨z, hzw', rfl⟩
    exact closure_mono (interior_mono (image_mono (hVT w' hw'))) hzin
  have hcrossPΘ : ∀ x ∈ frontier (c '' fbl s) ∩ Θ,
      HasPLCrossingAt (frontier (c '' fbl s)) Θ x := by
    intro x hx
    rw [hZc] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hcrossΘ y hy
  obtain ⟨ι, hιfin, C, hC, hCd, hCeq⟩ := exists_iUnion_isPLSphere_one_of_forall_lineChart
    (hPb.isPolyhedron.frontier.inter hΘtor.1) hcrossPΘ fun x hx =>
      (hcrossPΘ x hx).exists_lineChart hx.1
        (hPb.isPLSphere_frontier.exists_isOpen_inter_homeomorph_of_two hx.1) hTcl (hcTreg x hx.2)
  have hZP' : frontier (c '' fbl s) ∩ Θ ∩ P' = frontier (c '' fbl s) ∩ Θ ∩ Oc := by
    rw [← hk3]
    ext x
    constructor
    · rintro ⟨hx, hxΘ⟩
      have h1 : x ∈ frontier P' ∩ Oc := ⟨hx, hk2 ⟨hx, hxΘ⟩⟩
      rw [hfrO] at h1
      exact ⟨⟨h1.1, hxΘ⟩, h1.2⟩
    · rintro ⟨⟨hx, hxΘ⟩, hxO⟩
      have h1 : x ∈ frontier (c '' fbl s) ∩ Oc := ⟨hx, hxO⟩
      rw [← hfrO] at h1
      exact ⟨h1.1, hxΘ⟩
  have hsymmΘ : c.symm '' Θ = frontier T := by
    rw [← hΘeq]
    exact c.symm_image_image_of_subset_source hfrTc
  have hΘS : c.symm '' Θ ⊆ T := by
    rw [hsymmΘ]
    exact hTcomp.isClosed.frontier_subset
  have hZS : CarriesFirstHomologyOnto (c.symm '' (frontier (c '' fbl s) ∩ Θ)) T := by
    rw [hZc]
    convert hf7 s using 1
    exact c.symm_image_image_of_subset_source (inter_subset_right.trans hfrTc)
  have hWS : CarriesFirstHomologyOnto (c.symm '' (P' ∩ Θ)) T := by
    have hFint : CarriesFirstHomologyOnto (c.symm '' P' ∩ interior T) T :=
      (carriesFirstHomologyOnto_image_simplexRim hh hcut hgraph s).mono
        (fun y hy => ⟨interior_subset (hFrim hy), hrimT s hy⟩)
        (inter_subset_right.trans interior_subset)
    obtain ⟨A, B, hAfin, hBA, hAsp, hBsp⟩ :=
      exists_simplicialComplex_subcomplex_of_isPolyhedron
        (hP'poly.inter hTsolid.isPolyhedron) (hP'poly.inter hΘtor.1)
        (inter_subset_inter_right _ hTcl.frontier_subset)
    have : Finite A.faces := hAfin.to_subtype
    have hcF : c '' (c.symm '' P') = P' := c.image_symm_image_of_subset_target hP't
    have hA : A.space = c '' (c.symm '' P' ∩ T) := by
      rw [c.injOn.image_inter hFc hTc, hcF, hAsp]
    have hB : B.space = c '' (c.symm '' P' ∩ frontier T) := by
      rw [c.injOn.image_inter hFc hfrTc, hcF, hΘeq, hBsp]
    have hcarry := hFint.inter_frontier_of_chart hFcell.isCompact.isClosed hTcomp.isClosed
      hFcell.subsingleton_integralSingularHomology_one hFc A B hBA hA hB
    convert hcarry using 1
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxΘ⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rw [← hsymmΘ]
      exact ⟨x, hxΘ, rfl⟩
    · rintro ⟨hy, hyT⟩
      have hyc := hFc hy
      exact ⟨c y, ⟨(hmemF y hyc).mp hy, (hmemT y hyc).mp hyT⟩, c.left_inv hyc⟩
  have hfrZ : ∀ x ∈ P' ∩ Θ, x ∉ interior P' → x ∈ frontier (c '' fbl s) ∩ Θ := by
    intro x hx hxi
    have hxfr : x ∈ frontier P' ∩ Θ := by
      refine ⟨?_, hx.2⟩
      rw [hP'c.frontier_eq]
      exact ⟨hx.1, hxi⟩
    rw [hk3] at hxfr
    exact hxfr.1
  have h7' := hΘtor.carriesFirstHomologyOnto_image_inter_of_isClopen hC hCd hCeq
    inter_subset_right hP'c hOc hZP' hfrZ (c.continuousOn_symm.mono hΘt)
    (c.symm.injOn.mono hΘt) hΘS hZS hWS
  have h7 : CarriesFirstHomologyOnto (c.symm '' frontier P' ∩ frontier T) T := by
    convert h7' using 1
    rw [← hk3]
    ext y
    constructor
    · rintro ⟨hy, hyT⟩
      have hyc := hFc (hFbF hy)
      exact ⟨c y, ⟨(hmemFb y hyc).mp hy, (hmemT y hyc).mp hyT⟩, c.left_inv hyc⟩
    · rintro ⟨x, ⟨hx, hxΘ⟩, rfl⟩
      refine ⟨⟨x, hx, rfl⟩, ?_⟩
      rw [← hsymmΘ]
      exact ⟨x, hxΘ, rfl⟩
  refine ⟨Function.update fbl s (c.symm '' P'), Function.update fblBd s (c.symm '' frontier P'),
    section34FaceBallInvariants_update_of_subset hinv hFcell hFrim hFs h5 h6 h7 h8 h9,
    fun s' hs' => ⟨Function.update_of_ne hs' _ _, Function.update_of_ne hs' _ _⟩, ?_, ?_⟩
  · simp only [section34TraceCount, section34TraceComponents, Function.update_self]
    exact hcount
  · simp only [section34CrossingCount, Function.update_self]
    exact hpcount

end Compression

end DifferentialGeometry.Topology.PiecewiseLinear
