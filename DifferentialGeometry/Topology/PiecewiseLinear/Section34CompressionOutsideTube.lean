/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionOutside
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ThroughTube
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ExteriorComponent
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarEmbedding
import DifferentialGeometry.Topology.PiecewiseLinear.ExistsCombinatorialTriangulation
import DifferentialGeometry.Topology.BicollaredComplement

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem frontier_inter_eq_of_inter_eq {A B V : Set E3} (hV : IsOpen V) (h : A ∩ V = B ∩ V) :
    frontier A ∩ V = frontier B ∩ V := by
  have hcl : ∀ C : Set E3, closure C ∩ V = closure (C ∩ V) ∩ V := by
    intro C
    apply Subset.antisymm
    · rintro x ⟨hx, hxV⟩
      exact ⟨by rw [inter_comm]; exact hV.inter_closure ⟨hxV, hx⟩, hxV⟩
    · exact inter_subset_inter_left _ (closure_mono inter_subset_left)
  have hint : ∀ C : Set E3, interior C ∩ V = interior (C ∩ V) := by
    intro C
    rw [interior_inter, hV.interior_eq]
  ext x
  constructor
  · rintro ⟨⟨hxc, hxi⟩, hxV⟩
    refine ⟨⟨?_, fun hxi' => hxi ?_⟩, hxV⟩
    · have := (hcl A).subset ⟨hxc, hxV⟩
      rw [h] at this
      exact closure_mono inter_subset_left this.1
    · have := (hint B).subset ⟨hxi', hxV⟩
      rw [← h, ← hint A] at this
      exact this.1
  · rintro ⟨⟨hxc, hxi⟩, hxV⟩
    refine ⟨⟨?_, fun hxi' => hxi ?_⟩, hxV⟩
    · have := (hcl B).subset ⟨hxc, hxV⟩
      rw [← h] at this
      exact closure_mono inter_subset_left this.1
    · have := (hint A).subset ⟨hxi', hxV⟩
      rw [h, ← hint B] at this
      exact this.1

theorem frontier_sdiff_interior_of_subset_interior {W X : Set E3} (hWc : IsClosed W)
    (hXc : IsClosed X) (hXcl : closure (interior X) = X) (hXW : X ⊆ interior W) :
    frontier (W \ interior X) = frontier W ∪ frontier X := by
  have hc : IsClosed (W \ interior X) := hWc.sdiff isOpen_interior
  have hint : interior (W \ interior X) = interior W \ X := by
    rw [sdiff_eq, interior_inter, interior_compl, hXcl, ← sdiff_eq]
  rw [hc.frontier_eq, hint, hWc.frontier_eq, hXc.frontier_eq]
  ext x
  constructor
  · rintro ⟨⟨hxW, hxi⟩, hx⟩
    by_cases hxW' : x ∈ interior W
    · right
      have hxX : x ∈ X := by
        by_contra hxX
        exact hx ⟨hxW', hxX⟩
      exact ⟨hxX, hxi⟩
    · exact Or.inl ⟨hxW, hxW'⟩
  · rintro (⟨hxW, hxW'⟩ | ⟨hxX, hxi⟩)
    · refine ⟨⟨hxW, fun h => hxW' (hXW (interior_subset h))⟩, fun h => hxW' h.1⟩
    · exact ⟨⟨interior_subset (hXW hxX), hxi⟩, fun h => h.2 hxX⟩

theorem isConnected_compl_of_isCombinatorialSolidTorus {S : Set E3}
    (hS : IsCombinatorialSolidTorus S) : IsConnected Sᶜ := by
  have hSc : IsCompact S := hS.isPolyhedron.isCompact
  have hΘ : IsPLTorus (frontier S) := hS.isPLTorus_frontier
  obtain ⟨L, hLfin, hLcomb, hLconn, hLspace⟩ := hΘ.exists_combinatorial_triangulation
  let _ : Finite L.faces := hLfin.to_subtype
  have hpoly : IsPolyhedralManifold (n := 3) 2 (frontier S) := by
    have hLt : L.space ⊆ (chartAt (EuclideanSpace ℝ (Fin 3)) (0 : E3)).target := by
      rw [chartAt_self_eq]
      exact subset_univ _
    have h : IsPolyhedralManifold (n := 3) 2
        ((chartAt (EuclideanSpace ℝ (Fin 3)) (0 : E3)).symm '' L.space) :=
      ⟨⟨3, chartPieceOfComplex _ (chart_mem_atlas _ _) L hLt⟩, hLcomb⟩
    rw [← hLspace]
    simpa only [chartAt_self_eq, OpenPartialHomeomorph.refl_symm,
      OpenPartialHomeomorph.refl_apply, image_id] using h
  have hconn : IsConnected (frontier S) := hΘ.isPathConnected.isConnected
  have hbi := hpoly.isBicollared (hpoly.isTwoSided hconn)
  obtain ⟨-, n, hn3, C, -, hCS, hCball, -⟩ := hS
  have hint : (interior S).Nonempty := by
    obtain ⟨p, hp⟩ := (hCball ⟨0, by omega⟩).interior_nonempty
    rw [← hCS]
    exact ⟨p, interior_mono (subset_iUnion (fun i => (C i).space) ⟨0, by omega⟩) hp⟩
  exact isConnected_compl_of_isBicollared_frontier hSc.isClosed
    (hSc.of_isClosed_subset isClosed_frontier hSc.isClosed.frontier_subset) hconn hint
    (nonempty_compl.mpr hSc.ne_univ) hbi

theorem exists_reroute_push_push {M : Type*} [TopologicalSpace M] [T2Space M]
    {c : OpenPartialHomeomorph M E3} {Hs Obs Mk : Set M}
    {R₁ Lr₁ Bh₁ T₁ R₂ Lr₂ Bh₂ T₂ : Set E3} {g₁ g₂ : E3 → E3}
    (hR₁o : IsOpen R₁) (hclR₁ : closure R₁ ⊆ R₁ ∪ Bh₁ ∪ Lr₁)
    (hclR₁c : IsCompact (closure R₁)) (hclR₁t : closure R₁ ⊆ c.target) (hLr₁t : Lr₁ ⊆ c.target)
    (hT₁t : T₁ ⊆ c.target) (hBh₁ : c.symm '' Bh₁ ⊆ Obs)
    (hg₁c : ContinuousOn g₁ (R₁ ∪ Lr₁)) (hg₁Lr : ∀ y ∈ Lr₁, g₁ y = y) (hg₁R : MapsTo g₁ R₁ R₁)
    (hg₁T : ∀ y ∈ R₁, g₁ y ∉ T₁) (hT₁R : T₁ ⊆ R₁ ∪ Bh₁) (hR₁H : c.symm '' R₁ ⊆ Hs)
    (hR₁obs : c.symm '' R₁ ⊆ Obs ∨ Disjoint (c.symm '' R₁) Obs)
    (hR₁fr : Disjoint (c.symm '' R₁) (frontier Hs)) (hMk₁ : Disjoint Mk (c.symm '' R₁))
    (hR₂o : IsOpen R₂) (hclR₂ : closure R₂ ⊆ R₂ ∪ Bh₂ ∪ Lr₂)
    (hclR₂c : IsCompact (closure R₂)) (hclR₂t : closure R₂ ⊆ c.target) (hLr₂t : Lr₂ ⊆ c.target)
    (hT₂t : T₂ ⊆ c.target) (hBh₂ : c.symm '' Bh₂ ⊆ Obs)
    (hg₂c : ContinuousOn g₂ (R₂ ∪ Lr₂)) (hg₂Lr : ∀ y ∈ Lr₂, g₂ y = y) (hg₂R : MapsTo g₂ R₂ R₂)
    (hg₂T : ∀ y ∈ R₂, g₂ y ∉ T₂) (hT₂R : T₂ ⊆ R₂ ∪ Bh₂) (hR₂H : c.symm '' R₂ ⊆ Hs)
    (hR₂obs : c.symm '' R₂ ⊆ Obs ∨ Disjoint (c.symm '' R₂) Obs)
    (hR₂fr : Disjoint (c.symm '' R₂) (frontier Hs)) (hMk₂ : Disjoint Mk (c.symm '' R₂))
    (hR₂T₁ : Disjoint R₂ T₁) :
    ∃ r : M → M, ContinuousOn r (Hs \ Obs) ∧
      MapsTo r (Hs \ Obs) (Hs \ (Obs ∪ c.symm '' (T₁ ∪ T₂))) ∧
      (∀ z ∈ frontier Hs, r z = z) ∧ ∀ y ∈ Mk, r y = y := by
  obtain ⟨r₁, hr₁c, hr₁m, hr₁fr, hr₁k, -⟩ :=
    exists_reroute_push hR₁o hclR₁ hclR₁c hclR₁t hLr₁t hT₁t hBh₁ hg₁c hg₁Lr hg₁R hg₁T hT₁R hR₁H
      hR₁obs hR₁fr hMk₁
  obtain ⟨r₂, hr₂c, hr₂m, hr₂fr, hr₂k, hr₂id, hr₂in⟩ :=
    exists_reroute_push hR₂o hclR₂ hclR₂c hclR₂t hLr₂t hT₂t hBh₂ hg₂c hg₂Lr hg₂R hg₂T hT₂R hR₂H
      hR₂obs hR₂fr hMk₂
  have hR₂t : R₂ ⊆ c.target := subset_closure.trans hclR₂t
  have hr₂Z : ∀ y ∈ Hs \ (Obs ∪ c.symm '' T₁), r₂ y ∉ c.symm '' T₁ := by
    intro y hy
    have hyD : y ∈ Hs \ Obs := ⟨hy.1, fun h' => hy.2 (Or.inl h')⟩
    by_cases hyR : y ∈ c.symm '' R₂
    · obtain ⟨x', hx', hx'e⟩ := hr₂in y hyD hyR
      rintro ⟨x, hx, hxe⟩
      rw [← hxe] at hx'e
      have hxx := c.symm.injOn (hR₂t hx') (hT₁t hx) hx'e
      rw [hxx] at hx'
      exact Set.disjoint_left.mp hR₂T₁ hx' hx
    · rw [hr₂id y hyD hyR]
      exact fun h' => hy.2 (Or.inr h')
  obtain ⟨r, hrc, hrm, hrfr, hrk⟩ :=
    exists_reroute_comp hr₁c hr₁m hr₁fr hr₁k hr₂c hr₂m hr₂fr hr₂k hr₂Z
  refine ⟨r, hrc, fun y hy => ?_, hrfr, hrk⟩
  have h1 := hrm hy
  refine ⟨h1.1, fun h2 => h1.2 ?_⟩
  rw [image_union] at h2
  rcases h2 with h2 | h2 | h2
  · exact Or.inl h2
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr h2)

section OutsideTube

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η ψ : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

theorem exists_section34Compression_of_disjoint_of_uncleanPocket
    (hh : Topology.IsEmbedding (U.domRestrict h))
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
    (hDo : ∀ s' : Section34SimplexIndex 𝒦 3, s' ≠ s → Disjoint (Dj \ Jd) (fbl s'))
    (hout : Disjoint (Dj \ Jd) (fbl s)) (t₀ : Section34SimplexIndex 𝒦 4)
    (hst₀ : Section34Incident s.1 t₀.1) {c : OpenPartialHomeomorph M₂ E3}
    (hc : c ∈ (plGroupoid 3).maximalAtlas M₂) (hHc : H t₀.1 ⊆ c.source)
    (hfsc : fbl s ⊆ c.source)
    (hTc : section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source)
    (hTcomp : IsCompact (section34FaceTorus (section34VertexBallImage src f₁) s)) {O₀ : Set M₂}
    (hO₀def : O₀ = interior (H t₀.1) \ ⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
      (section34VertexBallImage src f₁ w' ∩ H t₀.1).Nonempty ∧ ¬ Section34Incident w'.1 s.1},
      section34VertexBallImage src f₁ w') (hO₀ : IsOpen O₀) (hfO₀ : fbl s ⊆ O₀)
    (hSgO₀ : frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ O₀ =
      frontier (section34FaceTorus (section34VertexBallImage src f₁) s) ∩ O₀)
    {Q : Set M₂} (hQcell : IsPLCellOn 3 Q (frontier Q)) (hQfr : frontier Q ⊆ Dj ∪ fblBd s)
    (hQP : Disjoint (interior (fbl s)) Q) (hQH : Q ⊆ interior (H t₀.1))
    (hunclean : ¬ (Disjoint (interior Q)
      (frontier (section34FaceTorus (section34VertexBallImage src f₁) s)) ∧
      ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 s.1 →
        Disjoint Q (section34VertexBallImage src f₁ u))) :
    ∃ fbl' fblBd' : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34TraceCount (section34VertexBallImage src f₁) fblBd' s + 1 ≤
        section34TraceCount (section34VertexBallImage src f₁) fblBd s ∧
      section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd' s ≤
        section34CrossingCount (section34SplitDiskImage srcBd f₁) fblBd s := by
  classical
  obtain ⟨hfcell, hfrim, hfV, hf4, hf5, -, hf7, -, -, hext⟩ := id hinv
  obtain ⟨-, hsubdiv, hmap, hcell, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hends, -, -⟩ := id hcut
  obtain ⟨-, -, hf₁, -, -, hmark, -, -, hrimT, -, -, -, -, -⟩ := id hgraph
  obtain ⟨hsupp, -, -, -, hHcell, -⟩ := id hctrl
  obtain ⟨hext1, -, hext3⟩ := id hext
  set T := section34FaceTorus (section34VertexBallImage src f₁) s with hTdef
  set Sg := frontier (⋃ w', section34VertexBallImage src f₁ w') with hSgdef
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
  have hJdb : Jd ⊆ fblBd s := by
    rw [← hDJ]
    exact inter_subset_right
  have hJdD : Jd ⊆ Dj := by
    rw [← hDJ]
    exact inter_subset_left
  obtain ⟨yJ, hyJ⟩ : Jd.Nonempty := by
    obtain ⟨P0, r0, u0, -, -, -, hB⟩ := id hDcell
    rw [hB]
    exact ⟨u0 (r0 (Pi.single 0 1)), r0 (Pi.single 0 1),
      ⟨Pi.single 0 1, ⟨Convexity.StdSimplex.single_mem_coordinateSet ℝ 0, 1,
        Pi.single_eq_of_ne (show (1 : Fin 3) ≠ 0 by decide) (1 : ℝ)⟩, rfl⟩, rfl⟩
  have hDwV : Dj ⊆ section34VertexBallImage src f₁ w := fun z hz =>
    image_mono (hcell (.vertexBall w)).boundary_subset (hDw hz)
  have hwinc : Section34Incident w.1 s.1 := by
    by_contra hn
    have hmem : yJ ∈ fbl s ∩ section34VertexBallImage src f₁ w :=
      ⟨hfbs (hJdb hyJ), hDwV (hJdD hyJ)⟩
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
  set Θ := frontier (c '' T) with hΘdef
  have hΘeq : c '' frontier T = Θ := c.image_frontier_of_isCompact hTcomp hTc
  have hfrTc : frontier T ⊆ c.source := hTcomp.isClosed.frontier_subset.trans hTc
  have hΘt : Θ ⊆ c.target := by
    rw [← hΘeq]
    rintro _ ⟨y, hy, rfl⟩
    exact c.map_source (hfrTc hy)
  have hΘtor : IsPLTorus Θ := by
    rw [← hΘeq]
    exact isPLTorus_image_frontier_section34FaceTorus hcut (hgraph.2.2.1) s hc hTc
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
  have hDjc : Dj ⊆ c.source := hDwV.trans (hVc w hwinc)
  obtain ⟨q, hq, hqJ⟩ := hDcell.exists_isPLHomeomorphOn_image_chart hc hDjc
  have hDjfbl : Dj ∩ fbl s = Jd := by
    apply Subset.antisymm
    · rintro z ⟨hzD, hzf⟩
      by_contra hzJ
      exact Set.disjoint_left.mp hout ⟨hzD, hzJ⟩ hzf
    · exact fun z hz => ⟨hJdD hz, hfbs (hJdb hz)⟩
  have hDP : c '' Dj ∩ c '' fbl s = q '' stdSimplexBoundary 2 := by
    rw [← c.injOn.image_inter hDjc hfsc, hDjfbl, hqJ]
  obtain ⟨hVwb, hVwfr⟩ := (hVcell w).isPLBall_image_chart hc (hVc w hwinc)
  have hDV : c '' Dj ⊆ frontier (c '' section34VertexBallImage src f₁ w) := by
    rw [← hVwfr]
    exact image_mono hDw
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
      ⟨hDO ⟨z, hz, rfl⟩, hDV ⟨z, hz, rfl⟩⟩
    rw [← hΘO] at hzc
    exact (hmemT z (hDjc hz)).mpr hzc.2
  have hJdSg : Jd ⊆ Sg := fun z hz =>
    (hmemSg z (hfbs (hJdb hz))).mpr ((hmemT z (hDjc (hJdD hz))).mp (hDjT (hJdD hz)))
  have hcrossΘJ : ∀ x ∈ q '' stdSimplexBoundary 2,
      HasPLCrossingAt (frontier (c '' fbl s)) Θ x := by
    intro x hx
    rw [← hqJ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hcrossΘ y ⟨hJdb hy, hDjT (hJdD hy)⟩
  have hcrossVP : ∀ x ∈ q '' stdSimplexBoundary 2,
      HasPLCrossingAt (frontier (c '' section34VertexBallImage src f₁ w))
        (frontier (c '' fbl s)) x := by
    intro x hx
    refine (hcrossΘJ x hx).symm.congr ?_ (Filter.Eventually.of_forall fun _ => Iff.rfl)
    have hxO : x ∈ Oo := by
      rw [← hqJ] at hx
      exact hDO (image_mono hJdD hx)
    filter_upwards [hOo.mem_nhds hxO] with z hz
    constructor
    · intro h1
      have h2 : z ∈ Oo ∩ Θ := ⟨hz, h1⟩
      rw [hΘO] at h2
      exact h2.2
    · intro h1
      have h2 : z ∈ Oo ∩ frontier (c '' section34VertexBallImage src f₁ w) := ⟨hz, h1⟩
      rw [← hΘO] at h2
      exact h2.2
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
  have hDEc : Disjoint (⋃ e ∈ {e : Section34EdgeIndex 𝒦 𝒦' |
      Section34Incident e.1 s.1}, c '' section34SplitDiskImage src f₁ e) (c '' Dj) := by
    refine Set.disjoint_right.mpr fun x hx hxE => ?_
    obtain ⟨e, he, z, hz, hzx⟩ := mem_iUnion₂.mp hxE
    obtain ⟨y, hy, rfl⟩ := hx
    have hzy := c.injOn (hEsc e he hz) (hDjc hy) hzx
    rw [hzy] at hz
    exact Set.disjoint_left.mp (hDE e) hy hz
  have hsTs : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      fbl s ⊆ interior (H t.1) := by
    intro t hst
    refine Subset.trans ?_ (hext1 t)
    unfold section34TetraObstacle
    exact subset_union_of_subset_right
      (subset_iUnion₂ (s := fun s' (_ : Section34Incident s'.1 t.1) => fbl s') s hst) _
  have hTsfin : {t : Section34SimplexIndex 𝒦 4 | Section34Incident s.1 t.1}.Finite := by
    obtain ⟨z, hz⟩ := (hfcell s).nonempty
    have himg : (Subtype.val '' {t : Section34SimplexIndex 𝒦 4 |
        Section34Incident s.1 t.1}).Finite := by
      refine (finite_setOf_carrier_inter_nonempty hctrl t₀.2.1).subset ?_
      rintro _ ⟨t, ht, rfl⟩
      exact ⟨t.2.1, z, interior_subset (hsTs t ht hz), interior_subset (hsTs t₀ hst₀ hz)⟩
    exact himg.of_finite_image Subtype.val_injective.injOn
  have hwt : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      Section34Incident w.1 t.1 :=
    fun t hst => hwinc.trans (convexHull_min hst (convex_convexHull ℝ _))
  have hVwt : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      section34VertexBallImage src f₁ w ⊆ interior (H t.1) := fun t hst =>
    image_vertexBall_subset_interior_of_incident hh hcut hctrl hgraph w t.2.1 (hwt t hst)
  set Qv := ⋃ u ∈ {u : Section34VertexIndex 𝒦 𝒦' | u ≠ w ∧
    (section34VertexBallImage src f₁ u ∩ H t₀.1).Nonempty}, section34VertexBallImage src f₁ u
    with hQvdef
  set Qf := ⋃ s' ∈ {s' : Section34SimplexIndex 𝒦 3 | s' ≠ s ∧ (fbl s' ∩ H t₀.1).Nonempty},
    fbl s' with hQfdef
  have hQvc : IsClosed Qv :=
    ((finite_setOf_vertexBallImage_inter_nonempty hctrl hgraph t₀.2.1).subset
      fun u hu => hu.2).isClosed_biUnion fun u _ => (hVcell u).isCompact.isClosed
  have hQfc : IsClosed Qf :=
    ((finite_setOf_faceBall_inter_nonempty hcut hctrl hext t₀.2.1).subset
      fun s' hs' => hs'.2).isClosed_biUnion fun s' _ => (hfcell s').isCompact.isClosed
  set OM := (⋂ t ∈ {t : Section34SimplexIndex 𝒦 4 | Section34Incident s.1 t.1},
    interior (H t.1)) ∩ O₀ ∩ (Qv ∪ Qf)ᶜ with hOMdef
  have hOMo : IsOpen OM :=
    ((hTsfin.isOpen_biInter fun t _ => isOpen_interior).inter hO₀).inter
      (hQvc.union hQfc).isOpen_compl
  have hDjOM : Dj ⊆ OM := by
    intro z hz
    refine ⟨⟨mem_iInter₂.mpr fun t ht => hVwt t ht (hDwV hz), ?_⟩, ?_⟩
    · rw [hO₀def]
      refine ⟨hVwt t₀ hst₀ (hDwV hz), fun hzQ => ?_⟩
      obtain ⟨u, ⟨-, hu⟩, hzu⟩ := mem_iUnion₂.mp hzQ
      have huw : u ≠ w := fun h => hu (h ▸ hwinc)
      exact Set.disjoint_left.mp (hDjV u huw) hz hzu
    · rintro (hzQ | hzQ)
      · obtain ⟨u, ⟨huw, -⟩, hzu⟩ := mem_iUnion₂.mp hzQ
        exact Set.disjoint_left.mp (hDjV u huw) hz hzu
      · obtain ⟨s', ⟨hs', -⟩, hzs'⟩ := mem_iUnion₂.mp hzQ
        by_cases hzJ : z ∈ Jd
        · have hzN := hf4 s s' (Ne.symm hs') ⟨hfbs (hJdb hzJ), hzs'⟩
          exact (hJdSg hzJ).2 hzN
        · exact Set.disjoint_left.mp (hDo s' hs') ⟨hz, hzJ⟩ hzs'
  set O := c '' (OM ∩ c.source) ∩ Oo with hOdef
  have hOo' : IsOpen O :=
    (c.isOpen_image_of_subset_source (hOMo.inter c.open_source) inter_subset_right).inter hOo
  have hDO' : c '' Dj ⊆ O := fun x hx => by
    obtain ⟨z, hz, rfl⟩ := hx
    exact ⟨⟨z, ⟨hDjOM hz, hDjc hz⟩, rfl⟩, hDO ⟨z, hz, rfl⟩⟩
  have hOsymm : ∀ x ∈ O, x ∈ c.target ∧ c.symm x ∈ OM := by
    rintro _ ⟨⟨z, hz, rfl⟩, -⟩
    exact ⟨c.map_source hz.2, by rw [c.left_inv hz.2]; exact hz.1⟩
  obtain ⟨Wc, Xc, Ein, Eout, Bin, Bout, Ain, Aout, Lin, Lout, Tin, Tout, hW, hX, hXW, hPX, hWeq,
    hWf, hXf, hEu, hEi, hEinB, hEoutB, hBAin, hBAout, hBinJ, hBoutJ, hEinc, hEoutc, hAinc,
    hAoutc, hLinc, hLoutc, hBinc, hBoutc, hsubO, hAVF, hLVF, hLinP, hLoutP, hYs, hYsf, R, Lr, g,
    hRo, hRO,
    hLrO, hToutR, hclR, hgc, hgLr, hgR, hgT, hRP, hRVF, hRV, hRY, hclRY, R', Lr', g', hR'o,
    hR'O, hLr'O, hTinR', hclR', hg'c, hg'Lr, hg'R, hg'T, hR'P, hR'VF, hR'V, hR'Y, -, hToutb, hToutf,
    hToutP, hLinT⟩ :=
    exists_compressionShell hPb hVwb hq hDV hDP hcrossVP hEcc hDEc hOo' hDO'
  have hAinO : Ain ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx)))))
  have hAoutO : Aout ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))
  have hLinO : Lin ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inl (Or.inr hx))))
  have hLoutO : Lout ⊆ O := fun x hx => hsubO (Or.inl (Or.inl (Or.inr hx)))
  have hTinO : Tin ⊆ O := fun x hx => hsubO (Or.inl (Or.inr hx))
  have hToutO : Tout ⊆ O := fun x hx => hsubO (Or.inr hx)
  have hOt : O ⊆ c.target := fun x hx => (hOsymm x hx).1
  have hOΘ : ∀ x ∈ O, (x ∈ Θ ↔ x ∈ frontier (c '' section34VertexBallImage src f₁ w)) := by
    intro x hx
    constructor
    · intro h1
      have h2 : x ∈ Oo ∩ Θ := ⟨hx.2, h1⟩
      rw [hΘO] at h2
      exact h2.2
    · intro h1
      have h2 : x ∈ Oo ∩ frontier (c '' section34VertexBallImage src f₁ w) := ⟨hx.2, h1⟩
      rw [← hΘO] at h2
      exact h2.2
  have hLΘ : ∀ x ∈ Lin ∪ Lout, x ∉ Θ := by
    intro x hx hxΘ
    have hxO : x ∈ O := hx.elim (fun h => hLinO h) (fun h => hLoutO h)
    exact Set.disjoint_left.mp hLVF hx (Or.inl ((hOΘ x hxO).mp hxΘ))
  have hAΘ : ∀ x ∈ Ain ∪ Aout, x ∈ Θ → x ∈ q '' stdSimplexBoundary 2 := by
    intro x hx hxΘ
    have hxO : x ∈ O := hx.elim (fun h => hAinO h) (fun h => hAoutO h)
    exact hAVF ⟨hx, Or.inl ((hOΘ x hxO).mp hxΘ)⟩
  have hPfrE : frontier (c '' fbl s) = Bin ∪ Ain ∪ (Bout ∪ Aout) := by
    rw [← hEu, hEinB, hEoutB]
  have hOMH : ∀ y ∈ OM, ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      y ∈ interior (H t.1) := fun y hy t ht => mem_iInter₂.mp hy.1.1 t ht
  have hOMV : ∀ y ∈ OM, ∀ u : Section34VertexIndex 𝒦 𝒦', u ≠ w →
      y ∉ section34VertexBallImage src f₁ u := by
    intro y hy u hu hyu
    have hyH := hOMH y hy t₀ hst₀
    exact hy.2 (Or.inl (mem_iUnion₂.mpr ⟨u, ⟨hu, y, hyu, interior_subset hyH⟩, hyu⟩))
  have hOMf : ∀ y ∈ OM, ∀ s' : Section34SimplexIndex 𝒦 3, s' ≠ s → y ∉ fbl s' := by
    intro y hy s' hs' hys'
    have hyH := hOMH y hy t₀ hst₀
    exact hy.2 (Or.inr (mem_iUnion₂.mpr ⟨s', ⟨hs', y, hys', interior_subset hyH⟩, hys'⟩))
  have hsplitV : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∀ y ∈ section34SplitDiskImage srcBd f₁ e,
      ∃ u : Section34VertexIndex 𝒦 𝒦', u ≠ w ∧ y ∈ section34VertexBallImage src f₁ u := by
    intro e y hy
    obtain ⟨u, u', huu', -, hDu⟩ := hends e
    obtain ⟨a, ha, rfl⟩ := image_mono (hcell (.splitDisk e)).boundary_subset hy
    rw [hDu] at ha
    by_cases huw : u = w
    · exact ⟨u', fun h => huu' (huw.trans h.symm), a, ha.2, rfl⟩
    · exact ⟨u, huw, a, ha.1, rfl⟩
  have hOsplit : ∀ x ∈ O, ∀ e : Section34EdgeIndex 𝒦 𝒦',
      x ∉ c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source) := by
    rintro x hxO e ⟨y, ⟨hye, hyc⟩, rfl⟩
    obtain ⟨u, hu, hyu⟩ := hsplitV e y hye
    have hyOM := (hOsymm _ hxO).2
    rw [c.left_inv hyc] at hyOM
    exact hOMV y hyOM u hu hyu
  have hJTr : q '' stdSimplexBoundary 2 ⊆ frontier (c '' fbl s) ∩ Θ := by
    intro x hx
    rw [← hqJ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(hmemP y (hDjc (hJdD hy))).mp (hJdb hy),
      (hmemT y (hDjc (hJdD hy))).mp (hDjT (hJdD hy))⟩
  have hcy₀ : c yJ ∈ q '' stdSimplexBoundary 2 := by
    rw [← hqJ]
    exact ⟨yJ, hyJ, rfl⟩
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
  have hZS : CarriesFirstHomologyOnto (c.symm '' (frontier (c '' fbl s) ∩ Θ)) T := by
    rw [hZc]
    convert hf7 s using 1
    exact c.symm_image_image_of_subset_source (inter_subset_right.trans hfrTc)
  have hΘS : c.symm '' Θ ⊆ T := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hΘeq] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    rw [c.left_inv (hfrTc hz)]
    exact hTcomp.isClosed.frontier_subset hz
  have hJsph : IsPLSphere 1 (q '' stdSimplexBoundary 2) :=
    hq.isPLSphere_image_stdSimplexBoundary (n := 1)
  have hDΘ : c '' Dj ⊆ Θ := by
    rw [← hΘeq]
    exact image_mono hDjT
  have hJD : q '' stdSimplexBoundary 2 ⊆ c '' Dj :=
    (image_mono fun _ hx => hx.1).trans hq.image_eq.subset
  have hDcl : IsClosed (c '' Dj) := (IsPLBall.isPolyhedron ⟨q, hq⟩).isClosed
  have hDJne : (c '' Dj \ q '' stdSimplexBoundary 2).Nonempty :=
    closure_nonempty_iff.mp ⟨c yJ, mem_closure_sdiff_image_stdSimplexBoundary hq hcy₀⟩
  have hDo' : ∀ z ∈ c '' Dj \ q '' stdSimplexBoundary 2, ∃ O' : Set E3, IsOpen O' ∧ z ∈ O' ∧
      O' ∩ Θ ⊆ c '' Dj := by
    intro z hz
    have hS := hVwb.isPLSphere_frontier
    have hint := hS.inter_closure_sdiff_eq_image_stdSimplexBoundary hq hDV
    refine ⟨Oo ∩ (closure (frontier (c '' section34VertexBallImage src f₁ w) \ c '' Dj))ᶜ,
      hOo.inter isClosed_closure.isOpen_compl, ⟨hDO hz.1, fun hzc => hz.2 ?_⟩, ?_⟩
    · rw [← hint]
      exact ⟨hz.1, hzc⟩
    · rintro y ⟨⟨hyO, hycl⟩, hyΘ⟩
      have h2 : y ∈ Oo ∩ Θ := ⟨hyO, hyΘ⟩
      rw [hΘO] at h2
      by_contra hyD
      exact hycl (subset_closure ⟨h2.2, hyD⟩)
  have hΘD : (Θ \ c '' Dj).Nonempty := by
    obtain ⟨p, hp⟩ := hJsph.nonempty
    obtain ⟨U₁, φ, r, hU₁, hpU₁, hr, hφ, hφp, hloc⟩ :=
      exists_quadrantChart hPb hVwb hq hDV hDP hp (hcrossVP p hp)
    have hpOo : p ∈ Oo := hDO (hJD hp)
    have hopen : IsOpen (φ '' (U₁ ∩ Oo)) :=
      hφ.isOpen_image_of_isOpen Metric.isOpen_ball (hU₁.inter hOo) inter_subset_left
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 ⟨p, ⟨hpU₁, hpOo⟩, hφp⟩
    have hmem : ((0 : ℝ), ε / 2, (0 : ℝ)) ∈ Metric.ball (0 : ℝ × ℝ × ℝ) ε := by
      rw [mem_ball_zero_iff, Prod.norm_def, Prod.norm_def]
      simp only [norm_zero, Real.norm_eq_abs]
      have h1 : |ε / 2| < ε := by rw [abs_of_pos (by linarith)]; linarith
      exact max_lt hε (max_lt h1 hε)
    obtain ⟨z, ⟨hzU, hzO⟩, hzφ⟩ := hball hmem
    obtain ⟨h1, -, -, -, h5⟩ := hloc z hzU
    refine ⟨z, ?_, fun hzD => ?_⟩
    · have hzV : z ∈ frontier (c '' section34VertexBallImage src f₁ w) :=
        h1.mpr (by rw [hzφ])
      have h3 : z ∈ Oo ∩ frontier (c '' section34VertexBallImage src f₁ w) := ⟨hzO, hzV⟩
      rw [← hΘO] at h3
      exact h3.2
    · have h6 := (h5.mp hzD).2
      rw [hzφ] at h6
      change ε / 2 ≤ 0 at h6
      linarith
  have hJo : ∃ O' : Set E3, IsOpen O' ∧ q '' stdSimplexBoundary 2 ⊆ O' ∧
      frontier (c '' fbl s) ∩ Θ ∩ O' ⊆ q '' stdSimplexBoundary 2 := by
    refine ⟨(Bin ∪ Bout)ᶜ, (hBinc.union hBoutc).isOpen_compl, fun x hx hxB => ?_, ?_⟩
    · rcases hxB with h | h
      · exact Set.disjoint_left.mp hBinJ h hx
      · exact Set.disjoint_left.mp hBoutJ h hx
    · rintro x ⟨⟨hxP, hxΘ⟩, hxO⟩
      rw [hPfrE] at hxP
      rcases hxP with (hxB | hxA) | (hxB | hxA)
      · exact absurd (Or.inl hxB) hxO
      · exact hAΘ x (Or.inl hxA) hxΘ
      · exact absurd (Or.inr hxB) hxO
      · exact hAΘ x (Or.inr hxA) hxΘ
  have hcarry : CarriesFirstHomologyOnto
      (c.symm '' ((frontier (c '' fbl s) ∩ Θ) \ q '' stdSimplexBoundary 2)) T :=
    hΘtor.carriesFirstHomologyOnto_image_sdiff_of_disk (Tr := frontier (c '' fbl s) ∩ Θ)
      hC hCd hCeq.symm inter_subset_right hJsph.isConnected hJsph.isPolyhedron.isClosed hJTr hJo hDΘ
      hJD hDcl hDJne hDo' hΘD (c.continuousOn_symm.mono hΘt) (c.symm.injOn.mono hΘt) hΘS hZS
  have hy₀ : yJ ∈ fblBd s ∩ Sg := ⟨hJdb hyJ, hJdSg hyJ⟩
  have hPcl : IsClosed (c '' fbl s) := hPb.isPolyhedron.isClosed
  have hPt : c '' fbl s ⊆ c.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact c.map_source (hfsc hz)
  have hsymmP : c.symm '' (c '' fbl s) = fbl s := c.symm_image_image_of_subset_source hfsc
  have hrimP : c '' (h '' simplexRim 𝒦 s.1) ⊆ interior (c '' fbl s) := by
    rw [← c.image_interior_of_subset_source hfsc]
    exact image_mono (hfrim s)
  have hfrH : ∀ t : Section34SimplexIndex 𝒦 4, IsConnected (frontier (H t.1)) := by
    intro t
    obtain ⟨P0, r0, u0, hr0, hu0, hS0, hB0⟩ := hHcell t.1 t.2.1
    rw [hB0]
    exact ((isConnected_stdSimplexBoundary 1).image r0
      (hr0.isPiecewiseAffineOn.continuousOn.mono fun x hx => hx.1)).image u0
      (hu0.continuousOn.mono (by
        rintro _ ⟨x, hx, rfl⟩
        exact hr0.bijOn.mapsTo hx.1))
  have hVobs : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      section34VertexBallImage src f₁ w ⊆
        section34TetraObstacle (section34VertexBallImage src f₁) fbl t := fun t hst z hz =>
    Or.inl (mem_iUnion₂.mpr ⟨⟨(t, w), hwt t hst⟩, rfl, hz⟩)
  have hfobs : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      fbl s ⊆ section34TetraObstacle (section34VertexBallImage src f₁) fbl t := fun t hst z hz =>
    Or.inr (mem_iUnion₂.mpr ⟨s, hst, hz⟩)
  have hPfrf : ∀ x ∈ frontier (c '' fbl s), c.symm x ∈ fbl s := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hPcl.frontier_subset hx
    rw [c.left_inv (hfsc hz)]
    exact hz
  have hDsymm : c.symm '' (c '' Dj) = Dj := c.symm_image_image_of_subset_source hDjc
  obtain ⟨hHb, -⟩ := (hHcell t₀.1 t₀.2.1).isPLBall_image_chart hc hHc
  have hint₀ : c '' interior (H t₀.1) = interior (c '' H t₀.1) :=
    c.image_interior_of_subset_source hHc
  have hfrY : frontier (Xc ∪ Tin) ⊆ interior (c '' H t₀.1) := by
    rw [hYsf, ← hint₀]
    rintro x (⟨z, hz, rfl⟩ | hx)
    · exact ⟨z, hVwt t₀ hst₀ (hDwV hz), rfl⟩
    · obtain ⟨z, hz, rfl⟩ := hPcl.frontier_subset (hEu.subset (Or.inl hx))
      exact ⟨z, hsTs t₀ hst₀ hz, rfl⟩
  have hYH : Xc ∪ Tin ⊆ interior (c '' H t₀.1) := by
    have hsub := hHb.subset_of_isCompact_frontier_subset hYs.isPolyhedron.isCompact
      (hfrY.trans interior_subset)
    intro x hx
    by_cases hxi : x ∈ interior (Xc ∪ Tin)
    · exact interior_mono hsub hxi
    · exact hfrY ⟨subset_closure hx, hxi⟩
  have hYt : Xc ∪ Tin ⊆ c.target := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := interior_subset (hYH hx)
    exact c.map_source (hHc hz)
  have hXt : Xc ⊆ c.target := fun x hx => hYt (Or.inl hx)
  have hPW : c '' fbl s ⊆ Wc := fun x hx => by
    rw [hWeq]
    exact Or.inl (Or.inl (Or.inl hx))
  have hXW' : Xc ⊆ Wc := fun x hx => by
    rw [hWeq]
    exact Or.inl (Or.inl (Or.inr hx))
  have hTinW : Tin ⊆ Wc := fun x hx => by
    rw [hWeq]
    exact Or.inl (Or.inr hx)
  have hWt : Wc ⊆ c.target := by
    rw [hWeq]
    rintro x (((hx | hx) | hx) | hx)
    · exact hPt hx
    · exact hXt hx
    · exact hYt (Or.inr hx)
    · exact hOt (hToutO hx)
  have hDY : c '' Dj ⊆ Xc ∪ Tin := by
    intro x hx
    have hxf : x ∈ frontier (Xc ∪ Tin) := by
      rw [hYsf]
      exact Or.inl hx
    exact hYs.isPolyhedron.isClosed.frontier_subset hxf
  have hwne : ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 s.1 → u ≠ w :=
    fun u hu h' => hu (by rw [h']; exact hwinc)
  have hTinM : ∀ x ∈ Tin, c.symm x ∈ OM := fun x hx => (hOsymm x (hTinO hx)).2
  have hToutM : ∀ x ∈ Tout, c.symm x ∈ OM := fun x hx => (hOsymm x (hToutO hx)).2
  have hPsymm : ∀ x ∈ c '' fbl s, c.symm x ∈ fbl s := by
    rintro _ ⟨z, hz, rfl⟩
    rw [c.left_inv (hfsc hz)]
    exact hz
  have hQc : Q ⊆ c.source := hQH.trans (interior_subset.trans hHc)
  obtain ⟨hQb, hQfrc⟩ := hQcell.isPLBall_image_chart hc hQc
  have hQcfr : frontier (c '' Q) ⊆ c '' Dj ∪ frontier (c '' fbl s) := by
    rw [← hQfrc, ← hPfr]
    rintro _ ⟨y, hy, rfl⟩
    rcases hQfr hy with h' | h'
    · exact Or.inl ⟨y, h', rfl⟩
    · exact Or.inr ⟨y, h', rfl⟩
  have hQW : c '' Q ⊆ Wc := hW.subset_of_isCompact_frontier_subset hQb.isPolyhedron.isCompact
    (hQcfr.trans (union_subset (hDY.trans (union_subset hXW' hTinW))
      (hPcl.frontier_subset.trans hPW)))
  have hintQ : interior (c '' Q) = c '' interior Q := (c.image_interior_of_subset_source hQc).symm
  have hQintP : Disjoint (interior (c '' Q)) (c '' fbl s) := by
    have h1 : Disjoint (interior (c '' fbl s)) (c '' Q) := by
      rw [← c.image_interior_of_subset_source hfsc]
      refine Set.disjoint_left.mpr ?_
      rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy'⟩
      have hyy := c.injOn (hQc hy') (hfsc (interior_subset hy)) hyy'
      rw [hyy] at hy'
      exact Set.disjoint_left.mp hQP hy hy'
    refine Set.disjoint_left.mpr fun x hxi hxP => ?_
    have hxcl : x ∈ closure (interior (c '' fbl s)) := by
      rw [hPb.closure_interior_of_finrank (by simp)]
      exact hxP
    obtain ⟨z, hzQ, hzP⟩ := mem_closure_iff.mp hxcl _ isOpen_interior hxi
    exact Set.disjoint_left.mp h1 hzP (interior_subset hzQ)
  have hLoutP : ∃ l ∈ Lout, l ∉ c '' fbl s := by
    by_contra hno
    push Not at hno
    have hWP : Wc ⊆ c '' fbl s := hPb.subset_of_isCompact_frontier_subset
      hW.isPolyhedron.isCompact (by
        rw [hWf]
        rintro x (hx | hx)
        · exact hno x hx
        · exact hPcl.frontier_subset (hEu.subset (Or.inr (hEoutB.symm.subset (Or.inl hx)))))
    obtain ⟨y, hy⟩ := hX.interior_nonempty
    have hyP : y ∈ c '' fbl s := hWP (hXW' (interior_subset hy))
    have hycl : y ∈ closure (interior (c '' fbl s)) := by
      rw [hPb.closure_interior_of_finrank (by simp)]
      exact hyP
    obtain ⟨z, hzX, hzP⟩ := mem_closure_iff.mp hycl _ isOpen_interior hy
    exact Set.disjoint_left.mp hPX hzP (interior_subset hzX)
  have hQTout : Disjoint (interior (c '' Q)) (interior Tout) := by
    refine Set.disjoint_left.mpr fun z hzQ hzT => ?_
    have hToutPc : Disjoint (interior Tout) (c '' fbl s) := by
      refine Set.disjoint_left.mpr fun x hx hxP => ?_
      have hxA : x ∈ Aout := by
        rw [← hToutP]
        exact ⟨interior_subset hx, hxP⟩
      have hxfr : x ∈ frontier Tout := by
        rw [hToutf]
        exact Or.inl (Or.inr hxA)
      exact hxfr.2 hx
    have hToutD : Disjoint (interior Tout) (c '' Dj) := by
      refine Set.disjoint_left.mpr fun x hx hxD => ?_
      have hxfr : x ∈ frontier Tout := by
        rw [hToutf]
        exact Or.inl (Or.inl hxD)
      exact hxfr.2 hx
    have hdisj : Disjoint (interior Tout) (frontier (c '' Q)) := by
      refine Set.disjoint_left.mpr fun x hx hxf => ?_
      rcases hQcfr hxf with h' | h'
      · exact Set.disjoint_left.mp hToutD hx h'
      · exact Set.disjoint_left.mp hToutPc hx (hPcl.frontier_subset h')
    have hsub : interior Tout ⊆ interior (c '' Q) :=
      subset_interior_of_isPreconnected_of_disjoint_frontier
        (hToutb.isConnected_interior_of_finrank (by simp)).isPreconnected hdisj ⟨z, hzT, hzQ⟩
    have hToutQ : Tout ⊆ c '' Q := by
      rw [← hToutb.closure_interior_of_finrank (by simp)]
      exact closure_minimal (hsub.trans interior_subset) hQb.isPolyhedron.isClosed
    obtain ⟨l, hlL, hlP⟩ := hLoutP
    have hlT : l ∈ Tout := hToutb.isPolyhedron.isClosed.frontier_subset (by
      rw [hToutf]
      exact Or.inr hlL)
    have hlQ := hToutQ hlT
    have hlW : l ∈ frontier Wc := by
      rw [hWf]
      exact Or.inl hlL
    have hlfr : l ∈ frontier (c '' Q) :=
      ⟨subset_closure hlQ, fun hli => hlW.2 (interior_mono hQW hli)⟩
    rcases hQcfr hlfr with h' | h'
    · exact Set.disjoint_left.mp hLVF (Or.inr hlL) (Or.inl (hDV h'))
    · exact hlP (hPcl.frontier_subset h')
  have hQsub : interior (c '' Q) ⊆ Xc ∪ Tin := by
    intro x hx
    have hxW : x ∈ Wc := hQW (interior_subset hx)
    rw [hWeq] at hxW
    rcases hxW with ((hxP | hxX) | hxT) | hxT
    · exact absurd hxP (Set.disjoint_left.mp hQintP hx)
    · exact Or.inl hxX
    · exact Or.inr hxT
    · by_cases hxi : x ∈ interior Tout
      · exact absurd hxi (Set.disjoint_left.mp hQTout hx)
      · have hxf : x ∈ frontier Tout := ⟨subset_closure hxT, hxi⟩
        rw [hToutf] at hxf
        rcases hxf with (hxD | hxA) | hxL
        · exact hDY hxD
        · exact absurd (hPcl.frontier_subset (hEu.subset (Or.inr (hEoutB.symm.subset
            (Or.inr hxA))))) (Set.disjoint_left.mp hQintP hx)
        · exfalso
          have hlW : x ∈ frontier Wc := by
            rw [hWf]
            exact Or.inl hxL
          exact hlW.2 (interior_mono hQW hx)
  have hz : ∃ z ∈ interior (c '' Q), z ∉ c '' T := by
    rcases not_and_or.mp hunclean with h' | h'
    · rw [not_disjoint_iff] at h'
      obtain ⟨y, hyi, hyT⟩ := h'
      have hyc : y ∈ c.source := hQc (interior_subset hyi)
      have hcyi : c y ∈ interior (c '' Q) := by
        rw [hintQ]
        exact ⟨y, hyi, rfl⟩
      have hcyΘ : c y ∈ Θ := (hmemT y hyc).mp hyT
      have hcl : c y ∈ closure (c '' T)ᶜ := by
        rw [hΘdef, frontier_eq_closure_inter_closure] at hcyΘ
        exact hcyΘ.2
      obtain ⟨z, hzQ, hzT⟩ := mem_closure_iff.mp hcl _ isOpen_interior hcyi
      exact ⟨z, hzQ, hzT⟩
    · push Not at h'
      obtain ⟨u, hu, hne⟩ := h'
      rw [not_disjoint_iff] at hne
      obtain ⟨y, hyQ, hyu⟩ := hne
      have hyc : y ∈ c.source := hQc hyQ
      have hyfr : y ∉ frontier Q := by
        intro hyf
        rcases hQfr hyf with hyD | hyB
        · exact Set.disjoint_left.mp (hDjV u (hwne u hu)) hyD hyu
        · have hmem : y ∈ fbl s ∩ section34VertexBallImage src f₁ u := ⟨hfbs hyB, hyu⟩
          rw [hfV s u hu] at hmem
          exact hmem
      have hyi : y ∈ interior Q := by
        by_contra h''
        exact hyfr ⟨subset_closure hyQ, h''⟩
      have hyV : y ∈ closure (interior (section34VertexBallImage src f₁ u)) :=
        (hVcell u).subset_closure_interior hyu
      have hU' : IsOpen (c.source ∩ c ⁻¹' interior (c '' Q)) :=
        c.isOpen_inter_preimage isOpen_interior
      have hyU' : y ∈ c.source ∩ c ⁻¹' interior (c '' Q) := by
        refine ⟨hyc, ?_⟩
        change c y ∈ interior (c '' Q)
        rw [hintQ]
        exact ⟨y, hyi, rfl⟩
      obtain ⟨y', ⟨hy'c, hy'Q⟩, hy'V⟩ := mem_closure_iff.mp hyV _ hU' hyU'
      refine ⟨c y', hy'Q, ?_⟩
      rintro ⟨t, ht, hte⟩
      have htt := c.injOn (hTc ht) hy'c hte
      rw [htt] at ht
      obtain ⟨w', hw', hy'w'⟩ := hTinc y' ht
      have huw' : u ≠ w' := fun h'' => hu (h'' ▸ hw')
      have hemp := interior_image_vertexBall_inter_image_vertexBall hcut hgraph huw'
      exact (Set.eq_empty_iff_forall_notMem.mp hemp) y' ⟨hy'V, hy'w'⟩
  have hmainp : ∀ x ∈ Xc, x ∉ c '' T → ∃ p ∈ interior Xc, p ∉ c '' T := by
    intro x hx hxT
    have hxcl : x ∈ closure (interior Xc) := by
      rw [hX.closure_interior_of_finrank (by simp)]
      exact hx
    obtain ⟨p, hpT, hpX⟩ := mem_closure_iff.mp hxcl _ hTcl.isOpen_compl hxT
    exact ⟨p, hpX, hpT⟩
  obtain ⟨p, hpX, hpT⟩ : ∃ p ∈ interior Xc, p ∉ c '' T := by
    obtain ⟨z, hzi, hzT⟩ := hz
    rcases hQsub hzi with hzX | hzTin
    · exact hmainp z hzX hzT
    by_cases hzX : z ∈ Xc
    · exact hmainp z hzX hzT
    have hzD : z ∉ c '' Dj := fun h' =>
      hzT (image_mono (hDjT.trans hTcomp.isClosed.frontier_subset) h')
    have hzA : z ∉ Ain := fun h' => Set.disjoint_left.mp hQintP hzi
      (hPcl.frontier_subset (hEu.subset (Or.inl (hEinB.symm.subset (Or.inr h')))))
    have hzR : z ∈ R' := by
      rcases hTinR' hzTin with h' | h' | h'
      · exact h'
      · exact absurd h' hzD
      · exact absurd h' hzA
    have hR'V' : Disjoint R' (c '' section34VertexBallImage src f₁ w) := by
      rcases hR'V with h' | h'
      · exact absurd (image_mono (hVT w hwinc) (h' hzR)) hzT
      · exact h'
    have hz'R := hg'R hzR
    have hz'X : g' z ∈ Xc := by
      rcases interior_subset (hR'Y hz'R) with h' | h'
      · exact h'
      · exact absurd h' (hg'T z hzR)
    refine hmainp (g' z) hz'X ?_
    rintro ⟨t, ht, hte⟩
    obtain ⟨w', hw', htw'⟩ := hTinc t ht
    by_cases hww : w' = w
    · subst hww
      exact Set.disjoint_left.mp hR'V' hz'R ⟨t, htw', hte⟩
    · have hOM := (hOsymm _ (hR'O hz'R)).2
      rw [← hte, c.left_inv (hTc ht)] at hOM
      exact hOMV t hOM w' hww htw'
  have hTsolid := isCombinatorialSolidTorus_image_section34FaceTorus hcut (hgraph.2.2.1) s hc hTc
  have hTconn := isConnected_compl_of_isCombinatorialSolidTorus hTsolid
  obtain ⟨qq, hqq⟩ : (Wc ∪ c '' T)ᶜ.Nonempty :=
    nonempty_compl.mpr (hW.isPolyhedron.isCompact.union hcT).ne_univ
  have hqqW : qq ∉ Wc := fun h' => hqq (Or.inl h')
  have hqqT : qq ∉ c '' T := fun h' => hqq (Or.inr h')
  have hjoin : JoinedIn (c '' T)ᶜ p qq :=
    ((hTcl.isOpen_compl.isConnected_iff_isPathConnected).mp hTconn).joinedIn p hpT qq hqqT
  obtain ⟨Nt, hNtc, -, hNtT, -, hG⟩ := exists_isPLBall_sdiff_interior_tube
    (∅ : Finset (E3 × E3)) hX hW hXW hTcl c.open_target hWt hpX hqqW hjoin
  set G := Wc \ interior (Xc ∪ Nt) with hGdef
  have hNtc' : IsClosed Nt := hNtc.isClosed
  have hGcl : IsClosed G := hW.isPolyhedron.isClosed.sdiff isOpen_interior
  have hGsub : G ⊆ c '' fbl s ∪ (Tin ∪ Tout) := by
    rintro x ⟨hxW, hxi⟩
    rw [hWeq] at hxW
    rcases hxW with ((hxP | hxX) | hxT) | hxT
    · exact Or.inl hxP
    · have hxf : x ∈ frontier Xc :=
        ⟨subset_closure hxX, fun h' => hxi (interior_mono subset_union_left h')⟩
      rw [hXf] at hxf
      rcases hxf with hxL | hxB
      · exact Or.inr (Or.inl (hLinT hxL))
      · exact Or.inl (hPcl.frontier_subset (hEu.subset (Or.inl (hEinB.symm.subset
          (Or.inl hxB)))))
    · exact Or.inr (Or.inl hxT)
    · exact Or.inr (Or.inr hxT)
  have hGt : G ⊆ c.target := fun x hx => hWt hx.1
  have hGN : G ∩ Ntᶜ = (Wc \ interior Xc) ∩ Ntᶜ := by
    ext x
    constructor
    · rintro ⟨⟨hxW, hxi⟩, hxN⟩
      exact ⟨⟨hxW, fun h' => hxi (interior_mono subset_union_left h')⟩, hxN⟩
    · rintro ⟨⟨hxW, hxi⟩, hxN⟩
      refine ⟨⟨hxW, fun h' => hxi ?_⟩, hxN⟩
      have hO' : IsOpen (interior (Xc ∪ Nt) ∩ Ntᶜ) := isOpen_interior.inter hNtc'.isOpen_compl
      exact interior_maximal (fun y hy => (interior_subset hy.1).resolve_right hy.2) hO'
        ⟨h', hxN⟩
  have hfrG : frontier G ∩ Ntᶜ = (Lout ∪ Bout ∪ (Lin ∪ Bin)) ∩ Ntᶜ := by
    rw [frontier_inter_eq_of_inter_eq hNtc'.isOpen_compl hGN,
      frontier_sdiff_interior_of_subset_interior hW.isPolyhedron.isClosed
        hX.isPolyhedron.isClosed (hX.closure_interior_of_finrank (by simp)) hXW, hWf, hXf]
  have hΘT : Θ ⊆ c '' T := hTcl.frontier_subset
  have hGΘ : frontier G ∩ Θ = (Bin ∪ Bout) ∩ Θ := by
    ext x
    constructor
    · rintro ⟨hxf, hxΘ⟩
      have hxN : x ∉ Nt := fun h' => Set.disjoint_left.mp hNtT h' (hΘT hxΘ)
      rcases (hfrG.subset ⟨hxf, hxN⟩).1 with (hxL | hxB) | (hxL | hxB)
      · exact absurd hxΘ (hLΘ x (Or.inr hxL))
      · exact ⟨Or.inr hxB, hxΘ⟩
      · exact absurd hxΘ (hLΘ x (Or.inl hxL))
      · exact ⟨Or.inl hxB, hxΘ⟩
    · rintro ⟨hxB, hxΘ⟩
      have hxN : x ∉ Nt := fun h' => Set.disjoint_left.mp hNtT h' (hΘT hxΘ)
      refine ⟨(hfrG.symm.subset ⟨?_, hxN⟩).1, hxΘ⟩
      rcases hxB with hxB | hxB
      · exact Or.inr (Or.inr hxB)
      · exact Or.inl (Or.inr hxB)
  have hBΘ : (Bin ∪ Bout) ∩ Θ = (frontier (c '' fbl s) ∩ Θ) \ q '' stdSimplexBoundary 2 := by
    ext x
    constructor
    · rintro ⟨hxB, hxΘ⟩
      refine ⟨⟨?_, hxΘ⟩, fun hxJ => ?_⟩
      · rcases hxB with hxB | hxB
        · exact hEu.subset (Or.inl (hEinB.symm.subset (Or.inl hxB)))
        · exact hEu.subset (Or.inr (hEoutB.symm.subset (Or.inl hxB)))
      · rcases hxB with hxB | hxB
        · exact Set.disjoint_left.mp hBinJ hxB hxJ
        · exact Set.disjoint_left.mp hBoutJ hxB hxJ
    · rintro ⟨⟨hxP, hxΘ⟩, hxJ⟩
      rw [hPfrE] at hxP
      rcases hxP with (hxB | hxA) | (hxB | hxA)
      · exact ⟨Or.inl hxB, hxΘ⟩
      · exact absurd (hAΘ x (Or.inl hxA) hxΘ) hxJ
      · exact ⟨Or.inr hxB, hxΘ⟩
      · exact absurd (hAΘ x (Or.inr hxA) hxΘ) hxJ
  set Oc := (Nt ∪ (Lin ∪ Lout) ∪ (Ain ∪ Aout))ᶜ with hOcdef
  have hOc : IsOpen Oc :=
    ((hNtc'.union (hLinc.union hLoutc)).union (hAinc.union hAoutc)).isOpen_compl
  have hOcN : Oc ⊆ Ntᶜ := fun x hx h' => hx (Or.inl (Or.inl h'))
  have hfrO : frontier G ∩ Oc = frontier (c '' fbl s) ∩ Oc := by
    ext x
    constructor
    · rintro ⟨hxf, hxO⟩
      refine ⟨?_, hxO⟩
      rw [hPfrE]
      rcases (hfrG.subset ⟨hxf, hOcN hxO⟩).1 with (hxL | hxB) | (hxL | hxB)
      · exact absurd (Or.inl (Or.inr (Or.inr hxL))) hxO
      · exact Or.inr (Or.inl hxB)
      · exact absurd (Or.inl (Or.inr (Or.inl hxL))) hxO
      · exact Or.inl (Or.inl hxB)
    · rintro ⟨hxP, hxO⟩
      refine ⟨(hfrG.symm.subset ⟨?_, hOcN hxO⟩).1, hxO⟩
      rw [hPfrE] at hxP
      rcases hxP with (hxB | hxA) | (hxB | hxA)
      · exact Or.inr (Or.inr hxB)
      · exact absurd (Or.inr (Or.inl hxA)) hxO
      · exact Or.inl (Or.inr hxB)
      · exact absurd (Or.inr (Or.inr hxA)) hxO
  have hk2 : frontier G ∩ Θ ⊆ Oc := by
    intro x hx
    rw [hGΘ] at hx
    obtain ⟨hxB, hxΘ⟩ := hx
    rintro ((hxN | hxL | hxL) | hxA | hxA)
    · exact Set.disjoint_left.mp hNtT hxN (hΘT hxΘ)
    · exact hLΘ x (Or.inl hxL) hxΘ
    · exact hLΘ x (Or.inr hxL) hxΘ
    · have hxJ := hAΘ x (Or.inl hxA) hxΘ
      rcases hxB with hxB | hxB
      · exact Set.disjoint_left.mp hBinJ hxB hxJ
      · exact Set.disjoint_left.mp hBoutJ hxB hxJ
    · have hxJ := hAΘ x (Or.inr hxA) hxΘ
      rcases hxB with hxB | hxB
      · exact Set.disjoint_left.mp hBinJ hxB hxJ
      · exact Set.disjoint_left.mp hBoutJ hxB hxJ
  have hk4 : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      frontier G ∩ c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source) ⊆ Oc := by
    rintro e x ⟨hxf, hxE⟩ ((hxN | hxL | hxL) | hxA | hxA)
    · rcases hGsub (hGcl.frontier_subset hxf) with hxP | hxT | hxT
      · obtain ⟨y, ⟨hye, hyc⟩, rfl⟩ := hxE
        have hyf : y ∈ fbl s := by
          obtain ⟨y', hy', hyy⟩ := hxP
          rw [← c.injOn (hfsc hy') hyc hyy]
          exact hy'
        obtain ⟨u, u', -, -, hDu⟩ := hends e
        obtain ⟨a, ha, hay⟩ := image_mono (hcell (.splitDisk e)).boundary_subset hye
        rw [hDu] at ha
        have hyu : y ∈ section34VertexBallImage src f₁ u := ⟨a, ha.1, hay⟩
        have hinc : Section34Incident u.1 s.1 := by
          by_contra hn
          have hmem : y ∈ fbl s ∩ section34VertexBallImage src f₁ u := ⟨hyf, hyu⟩
          rw [hfV s u hn] at hmem
          exact hmem
        exact Set.disjoint_left.mp hNtT hxN ⟨y, hVT u hinc hyu, rfl⟩
      · exact hOsplit x (hTinO hxT) e hxE
      · exact hOsplit x (hToutO hxT) e hxE
    · exact hOsplit x (hLinO hxL) e hxE
    · exact hOsplit x (hLoutO hxL) e hxE
    · exact hOsplit x (hAinO hxA) e hxE
    · exact hOsplit x (hAoutO hxA) e hxE
  have hk3 : frontier G ∩ Θ = frontier (c '' fbl s) ∩ Θ ∩ (Bin ∪ Bout) := by
    rw [hGΘ]
    ext x
    constructor
    · rintro ⟨hxB, hxΘ⟩
      refine ⟨⟨?_, hxΘ⟩, hxB⟩
      rcases hxB with hxB | hxB
      · exact hEu.subset (Or.inl (hEinB.symm.subset (Or.inl hxB)))
      · exact hEu.subset (Or.inr (hEoutB.symm.subset (Or.inl hxB)))
    · rintro ⟨⟨-, hxΘ⟩, hxB⟩
      exact ⟨hxB, hxΘ⟩
  have hBP : Bin ∪ Bout ⊆ frontier (c '' fbl s) := by
    rintro x (hx | hx)
    · exact hEu.subset (Or.inl (hEinB.symm.subset (Or.inl hx)))
    · exact hEu.subset (Or.inr (hEoutB.symm.subset (Or.inl hx)))
  have hSel : IsCompact (Bin ∪ Bout) :=
    (hPb.isPolyhedron.isCompact.of_isClosed_subset isClosed_frontier
      hPcl.frontier_subset).of_isClosed_subset (hBinc.union hBoutc) hBP
  have hSelt : Bin ∪ Bout ⊆ c.target := fun x hx => hPt (hPcl.frontier_subset (hBP hx))
  have hy₀S : c yJ ∉ Bin ∪ Bout := by
    rintro (h' | h')
    · exact Set.disjoint_left.mp hBinJ h' hcy₀
    · exact Set.disjoint_left.mp hBoutJ h' hcy₀
  have h7 : CarriesFirstHomologyOnto (c.symm '' (frontier G ∩ Θ)) T := by
    rw [hGΘ, hBΘ]
    exact hcarry
  have hrimG : c '' (h '' simplexRim 𝒦 s.1) ⊆ interior G := by
    intro x hx
    have hxP := hrimP hx
    have hxT : x ∈ c '' T := by
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨y, interior_subset (hrimT s hy), rfl⟩
    have hxN : x ∉ Nt := fun h' => Set.disjoint_left.mp hNtT h' hxT
    have hO' : IsOpen (interior (c '' fbl s) ∩ Ntᶜ) := isOpen_interior.inter hNtc'.isOpen_compl
    refine interior_maximal (t := interior (c '' fbl s) ∩ Ntᶜ) (s := G) (fun y hy => ?_) hO'
      ⟨hxP, hxN⟩
    refine ⟨hPW (interior_subset hy.1), fun h' => ?_⟩
    rcases interior_subset h' with h'' | h''
    · exact Set.disjoint_left.mp hPX hy.1 h''
    · exact hy.2 h''
  have hGO₀ : c.symm '' G ⊆ O₀ := by
    rintro _ ⟨x, hx, rfl⟩
    rcases hGsub hx with hxP | hxT | hxT
    · exact hfO₀ (hPsymm x hxP)
    · exact (hTinM x hxT).1.2
    · exact (hToutM x hxT).1.2
  have hGZ : c.symm '' G ⊆ fbl s ∪ c.symm '' (Tin ∪ Tout) := by
    rintro _ ⟨x, hx, rfl⟩
    rcases hGsub hx with hxP | hxT
    · exact Or.inl (hPsymm x hxP)
    · exact Or.inr ⟨x, hxT, rfl⟩
  have hZV : ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 s.1 →
      Disjoint (c.symm '' (Tin ∪ Tout)) (section34VertexBallImage src f₁ u) := by
    intro u hu
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨x, hx | hx, rfl⟩ hxu
    · exact hOMV _ (hTinM x hx) u (hwne u hu) hxu
    · exact hOMV _ (hToutM x hx) u (hwne u hu) hxu
  have hZs : ∀ s', s' ≠ s → c.symm '' (Tin ∪ Tout) ∩ fbl s' ⊆
      interior (⋃ w', section34VertexBallImage src f₁ w') := by
    rintro s' hs' _ ⟨⟨x, hx | hx, rfl⟩, hy⟩
    · exact absurd hy (hOMf _ (hTinM x hx) s' hs')
    · exact absurd hy (hOMf _ (hToutM x hx) s' hs')
  have hZH : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 →
      c.symm '' (Tin ∪ Tout) ⊆ interior (H t.1) := by
    intro t hst
    rintro _ ⟨x, hx | hx, rfl⟩
    · exact hOMH _ (hTinM x hx) t hst
    · exact hOMH _ (hToutM x hx) t hst
  have hRM : ∀ S : Set E3, S ⊆ O → ∀ y ∈ c.symm '' S, y ∈ OM := by
    rintro S hSO _ ⟨x, hx, rfl⟩
    exact (hOsymm x (hSO hx)).2
  have hbdd : ∀ S : Set E3, S ⊆ O → closure S ⊆ c '' H t₀.1 := by
    intro S hSO
    refine closure_minimal (fun x hx => ?_) hHb.isPolyhedron.isClosed
    obtain ⟨⟨z, hz, rfl⟩, -⟩ := hSO hx
    exact ⟨z, interior_subset (hOMH z hz.1 t₀ hst₀), rfl⟩
  have hbddc : ∀ S : Set E3, S ⊆ O → IsCompact (closure S) := fun S hSO =>
    hHb.isPolyhedron.isCompact.of_isClosed_subset isClosed_closure (hbdd S hSO)
  have hbddt : ∀ S : Set E3, S ⊆ O → closure S ⊆ c.target := by
    intro S hSO x hx
    obtain ⟨z, hz, rfl⟩ := hbdd S hSO hx
    exact c.map_source (hHc hz)
  have hr : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 → ∃ r : M₂ → M₂,
      ContinuousOn r (H t.1 \ section34TetraObstacle (section34VertexBallImage src f₁) fbl t) ∧
      MapsTo r (H t.1 \ section34TetraObstacle (section34VertexBallImage src f₁) fbl t)
        (H t.1 \ (section34TetraObstacle (section34VertexBallImage src f₁) fbl t ∪
          c.symm '' (Tin ∪ Tout))) ∧
      (∀ z ∈ frontier (H t.1), r z = z) ∧
      ∀ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 t.1 →
        ∀ y ∈ h '' simplexBody 𝒦' u.1, r y = y := by
    intro t hst
    set Obs := section34TetraObstacle (section34VertexBallImage src f₁) fbl t with hObsdef
    set Mk := ⋃ (u : Section34VertexIndex 𝒦 𝒦') (_ : ¬ Section34Incident u.1 t.1),
      h '' simplexBody 𝒦' u.1 with hMkdef
    have hMkV : ∀ y ∈ Mk, ∃ u : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident u.1 s.1 ∧
        u ≠ w ∧ y ∈ section34VertexBallImage src f₁ u := by
      intro y hy
      obtain ⟨u, hu, hyu⟩ := mem_iUnion₂.mp hy
      have hus : ¬ Section34Incident u.1 s.1 := fun h' =>
        hu (h'.trans (convexHull_min hst (convex_convexHull ℝ _)))
      exact ⟨u, hus, hwne u hus, interior_subset (hmark u hyu)⟩
    have hMkR : ∀ S : Set E3, S ⊆ O → Disjoint Mk (c.symm '' S) := fun S hSO =>
      Set.disjoint_left.mpr fun y hy hyS => by
        obtain ⟨u, -, huw, hyu⟩ := hMkV y hy
        exact hOMV y (hRM S hSO y hyS) u huw hyu
    have hRobsG : ∀ S : Set E3, S ⊆ O → Disjoint S (c '' fbl s) →
        (S ⊆ c '' section34VertexBallImage src f₁ w ∨
          Disjoint S (c '' section34VertexBallImage src f₁ w)) →
        c.symm '' S ⊆ Obs ∨ Disjoint (c.symm '' S) Obs := by
      intro S hSO hSP hSV
      rcases hSV with hSV | hSV
      · left
        rintro _ ⟨x, hx, rfl⟩
        obtain ⟨z, hz, rfl⟩ := hSV hx
        rw [c.left_inv (hVc w hwinc hz)]
        exact hVobs t hst hz
      · right
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨x, hx, rfl⟩ hxo
        have hxM := (hOsymm x (hSO hx)).2
        rcases hxo with hxo | hxo
        · obtain ⟨pp, -, hpp⟩ := mem_iUnion₂.mp hxo
          by_cases hpw : pp.1.2 = w
          · rw [hpw] at hpp
            refine Set.disjoint_left.mp hSV hx ?_
            rw [← c.right_inv (hOt (hSO hx))]
            exact ⟨c.symm x, hpp, rfl⟩
          · exact hOMV _ hxM pp.1.2 hpw hpp
        · obtain ⟨s'', -, hs''⟩ := mem_iUnion₂.mp hxo
          by_cases hss : s'' = s
          · rw [hss] at hs''
            refine Set.disjoint_left.mp hSP hx ?_
            rw [← c.right_inv (hOt (hSO hx))]
            exact ⟨c.symm x, hs'', rfl⟩
          · exact hOMf _ hxM s'' hss hs''
    have hBh₁ : c.symm '' (c '' Dj ∪ Ain) ⊆ Obs := by
      rw [image_union, hDsymm]
      rintro y (hy | ⟨x, hx, rfl⟩)
      · exact hVobs t hst (hDwV hy)
      · exact hfobs t hst (hPfrf x (hEu.subset (Or.inl (hEinB.symm.subset (Or.inr hx)))))
    have hBh₂ : c.symm '' (c '' Dj ∪ Aout) ⊆ Obs := by
      rw [image_union, hDsymm]
      rintro y (hy | ⟨x, hx, rfl⟩)
      · exact hVobs t hst (hDwV hy)
      · exact hfobs t hst (hPfrf x (hEu.subset (Or.inr (hEoutB.symm.subset (Or.inr hx)))))
    have hRH : ∀ S : Set E3, S ⊆ O → c.symm '' S ⊆ H t.1 := fun S hSO y hy =>
      interior_subset (hOMH y (hRM S hSO y hy) t hst)
    have hRfr : ∀ S : Set E3, S ⊆ O → Disjoint (c.symm '' S) (frontier (H t.1)) := fun S hSO =>
      Set.disjoint_left.mpr fun y hy hyf => hyf.2 (hOMH y (hRM S hSO y hy) t hst)
    obtain ⟨r, hrc, hrm, hrfr, hrk⟩ := exists_reroute_push_push (c := c) (Hs := H t.1)
      (Obs := Obs) (Mk := Mk) hR'o hclR' (hbddc R' hR'O) (hbddt R' hR'O)
      (fun x hx => hOt (hLr'O hx)) (fun x hx => hOt (hTinO hx)) hBh₁ hg'c hg'Lr hg'R hg'T
      hTinR' (hRH R' hR'O) (hRobsG R' hR'O hR'P hR'V) (hRfr R' hR'O) (hMkR R' hR'O)
      hRo hclR (hbddc R hRO) (hbddt R hRO) (fun x hx => hOt (hLrO hx))
      (fun x hx => hOt (hToutO hx)) hBh₂ hgc hgLr hgR hgT hToutR (hRH R hRO)
      (hRobsG R hRO hRP hRV) (hRfr R hRO) (hMkR R hRO) (hRY.mono_right subset_union_right)
    exact ⟨r, hrc, hrm, hrfr, fun u hu y hy => hrk y (mem_iUnion₂.mpr ⟨u, hu, hy⟩)⟩
  exact exists_section34Compression_of_chartBall hinv s hc hfsc hTc hTcomp hfO₀ hSgO₀ hG hGt
    hGO₀ hrimG hGZ hZV hZs hZH hr hOc hfrO hk2 hk4 hk3 hSel hSelt hy₀ hy₀S h7

end OutsideTube

end DifferentialGeometry.Topology.PiecewiseLinear
