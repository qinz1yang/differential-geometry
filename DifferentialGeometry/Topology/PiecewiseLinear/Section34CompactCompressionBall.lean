/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSplitDiskIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallUpdate
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionPocket
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionReroute
import DifferentialGeometry.Topology.PiecewiseLinear.CurveCrossingGeneralPosition

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Push

theorem exists_compactPush {Obs R Lr Bh T : Set E3} {g : E3 → E3} (hRo : IsOpen R)
    (hclR : closure R ⊆ R ∪ Bh ∪ Lr) (hBh : Bh ⊆ Obs) (hgc : ContinuousOn g (R ∪ Lr))
    (hgLr : ∀ y ∈ Lr, g y = y) (hgR : MapsTo g R R) (hgT : ∀ y ∈ R, g y ∉ T)
    (hTR : T ⊆ R ∪ Bh) (hRobs : R ⊆ Obs ∨ Disjoint R Obs) :
    ∃ r : E3 → E3, ContinuousOn r Obsᶜ ∧ MapsTo r Obsᶜ (Obs ∪ T)ᶜ ∧ (∀ y ∉ R, r y = y) ∧
      MapsTo r R R := by
  classical
  refine ⟨R.piecewise g id, ?_, ?_, fun y hy => piecewise_eq_of_notMem R g id hy,
    fun y hy => by rw [piecewise_eq_of_mem R g id hy]; exact hgR hy⟩
  · refine continuousOn_of_isClosed_cover (isClosed_closure (s := R)) hRo.isClosed_compl
      (fun y _ => ?_) ?_ ?_
    · by_cases hyR : y ∈ R
      · exact Or.inl (subset_closure hyR)
      · exact Or.inr hyR
    · have hsub : Obsᶜ ∩ closure R ⊆ R ∪ Lr := by
        rintro y ⟨hy, hycl⟩
        rcases hclR hycl with (hyR | hyB) | hyL
        · exact Or.inl hyR
        · exact absurd (hBh hyB) hy
        · exact Or.inr hyL
      refine (hgc.mono hsub).congr fun y hy => ?_
      by_cases hyR : y ∈ R
      · exact piecewise_eq_of_mem R g id hyR
      · rw [piecewise_eq_of_notMem R g id hyR]
        rcases hsub hy with h | h
        · exact absurd h hyR
        · exact (hgLr y h).symm
    · exact continuousOn_id.congr fun y hy => piecewise_eq_of_notMem R g id hy.2
  · intro y hy
    by_cases hyR : y ∈ R
    · have hdis : Disjoint R Obs := hRobs.resolve_left fun h => hy (h hyR)
      rw [piecewise_eq_of_mem R g id hyR]
      rintro (h | h)
      · exact Set.disjoint_left.mp hdis (hgR hyR) h
      · exact hgT y hyR h
    · rw [piecewise_eq_of_notMem R g id hyR]
      rintro (h | h)
      · exact hy h
      · rcases hTR h with h' | h'
        · exact hyR h'
        · exact hy (hBh h')

end Push

section Spine

theorem IsSpine.eq_range {S J : Set E3} (hJ : IsSpine S J) :
    ∃ f : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → E3, Continuous f ∧ J = range f := by
  obtain ⟨φ, p, hp, rfl⟩ := hJ
  let p' : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := ⟨p, interior_subset hp⟩
  refine ⟨fun z => (φ (p', z) : E3), continuous_subtype_val.comp
    (φ.continuous.comp (continuous_const.prodMk continuous_id)), ?_⟩
  ext x
  constructor
  · rintro ⟨y, ⟨q, hq, rfl⟩, rfl⟩
    have hq' : q = (p', q.2) := Prod.ext (Subtype.ext hq) rfl
    exact ⟨q.2, congrArg (fun q => (φ q : E3)) hq'.symm⟩
  · rintro ⟨z, rfl⟩
    exact ⟨φ (p', z), ⟨(p', z), rfl, rfl⟩, rfl⟩

theorem IsSpine.isCompact {S J : Set E3} (hJ : IsSpine S J) : IsCompact J := by
  obtain ⟨f, hf, rfl⟩ := hJ.eq_range
  exact isCompact_range hf

theorem IsSpine.isConnected {S J : Set E3} (hJ : IsSpine S J) : IsConnected J := by
  obtain ⟨f, hf, rfl⟩ := hJ.eq_range
  have : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 zero_le_one)
  exact isConnected_range hf

end Spine

section Frontier

variable {K K' : Geometry.SimplicialComplex ℝ E3}

theorem frontier_iUnion_inter_eq_faceTorus_inter
    {tgtV : Section34CompactVertexIndex K K' → Set E3} (s : Section34CompactSimplexIndex K 3)
    {O : Set E3} (hO : IsOpen O)
    (hOV : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 s.1 →
      Disjoint O (tgtV w)) :
    frontier (⋃ w, tgtV w) ∩ O = frontier (section34CompactFaceTorus tgtV s) ∩ O := by
  have heq : (⋃ w, tgtV w) ∩ O = section34CompactFaceTorus tgtV s ∩ O := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxO⟩
      obtain ⟨w, hxw⟩ := mem_iUnion.mp hx
      by_cases hw : Section34Incident w.1 s.1
      · exact ⟨mem_iUnion₂.mpr ⟨⟨(s, w), hw⟩, rfl, hxw⟩, hxO⟩
      · exact absurd hxw (Set.disjoint_left.mp (hOV w hw) hxO)
    · rintro x ⟨hx, hxO⟩
      obtain ⟨a, -, hxa⟩ := mem_iUnion₂.mp hx
      exact ⟨mem_iUnion.mpr ⟨a.1.2, hxa⟩, hxO⟩
  rw [← frontier_inter_open_inter hO, heq, frontier_inter_open_inter hO]

theorem frontier_iUnion_inter_eq_vertexBall_inter
    {tgtV : Section34CompactVertexIndex K K' → Set E3} (w : Section34CompactVertexIndex K K')
    {O : Set E3} (hO : IsOpen O)
    (hOV : ∀ w' : Section34CompactVertexIndex K K', w' ≠ w → Disjoint O (tgtV w')) :
    frontier (⋃ w', tgtV w') ∩ O = frontier (tgtV w) ∩ O := by
  have heq : (⋃ w', tgtV w') ∩ O = tgtV w ∩ O := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxO⟩
      obtain ⟨w', hxw⟩ := mem_iUnion.mp hx
      by_cases hw : w' = w
      · exact ⟨hw ▸ hxw, hxO⟩
      · exact absurd hxw (Set.disjoint_left.mp (hOV w' hw) hxO)
    · exact inter_subset_inter_left _ (subset_iUnion tgtV w)
  rw [← frontier_inter_open_inter hO, heq, frontier_inter_open_inter hO]

variable {C : Set E3} {src srcBd : Section34CompactLabelOf K K' → Set E3} {f₁ : E3 → E3}

theorem Section34CompactCutFrame.interior_vertexBallImage_inter
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hf₁ : IsPLHomeomorphOn f₁ (section34CompactCutNeighborhood src)
      (f₁ '' section34CompactCutNeighborhood src))
    {w w' : Section34CompactVertexIndex K K'} (hww : w ≠ w') :
    interior (section34CompactVertexBallImage src f₁ w) ∩
      section34CompactVertexBallImage src f₁ w' = ∅ := by
  obtain ⟨-, -, -, -, -, -, hcell, hbd, -⟩ := id hcut
  have hN : ∀ v : Section34CompactVertexIndex K K',
      src (.vertexBall v) ⊆ section34CompactCutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (.vertexBall v)) v
  have hG := isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset hf₁
    (hcell (.vertexBall w)).isPolyhedron (hN w)
  have hint := ((hcell (.vertexBall w)).image_boundary_interior hG).2
  change interior (f₁ '' src (.vertexBall w)) ∩ f₁ '' src (.vertexBall w') = ∅
  rw [← hint]
  refine eq_empty_of_forall_notMem ?_
  rintro _ ⟨⟨q, ⟨hqV, hqB⟩, rfl⟩, q', hq', hqq'⟩
  have hqq : q' = q := hf₁.bijOn.injOn (hN w' hq') (hN w hqV) hqq'
  rw [hqq] at hq'
  obtain ⟨e, he⟩ := hcut.exists_splitDisk_eq_inter_vertexBall hww ⟨q, hqV, hq'⟩
  have hqe : q ∈ src (.splitDisk e) := by
    rw [he]
    exact ⟨hqV, hq'⟩
  have hsub : src (.splitDisk e) ⊆ src (.vertexBall w) := by
    rw [he]
    exact inter_subset_left
  apply hqB
  rw [hbd (.vertexBall w)]
  exact mem_iUnion₂.mpr ⟨.splitDisk e, ⟨hsub, by simp⟩, hqe⟩

end Frontier

section Exterior

variable {K K' : Geometry.SimplicialComplex ℝ E3} {h : E3 → E3}

open Classical in
theorem section34CompactTetraObstacle_update_subset
    {tgtV : Section34CompactVertexIndex K K' → Set E3}
    {fbl : Section34CompactSimplexIndex K 3 → Set E3} {s : Section34CompactSimplexIndex K 3}
    {F Z : Set E3} (hFZ : F ⊆ fbl s ∪ Z) (t : Section34CompactSimplexIndex K 4) :
    section34CompactTetraObstacle tgtV (Function.update fbl s F) t ⊆
      section34CompactTetraObstacle tgtV fbl t ∪ Z := by
  rintro x (hx | hx)
  · exact Or.inl (Or.inl hx)
  · obtain ⟨s', hs', hx'⟩ := mem_iUnion₂.mp hx
    by_cases hne : s' = s
    · rw [hne, Function.update_self] at hx'
      rcases hFZ hx' with hx'' | hx''
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨s, hne ▸ hs', hx''⟩))
      · exact Or.inr hx''
    · rw [Function.update_of_ne hne] at hx'
      exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨s', hs', hx'⟩))

open Classical in
theorem section34CompactTetraObstacle_update_of_not_incident
    {tgtV : Section34CompactVertexIndex K K' → Set E3}
    {fbl : Section34CompactSimplexIndex K 3 → Set E3} {s : Section34CompactSimplexIndex K 3}
    (F : Set E3) {t : Section34CompactSimplexIndex K 4} (hst : ¬ Section34Incident s.1 t.1) :
    section34CompactTetraObstacle tgtV (Function.update fbl s F) t =
      section34CompactTetraObstacle tgtV fbl t := by
  simp only [section34CompactTetraObstacle]
  congr 1
  refine iUnion₂_congr fun s' hs' => ?_
  have hne : s' ≠ s := by
    rintro rfl
    exact hst hs'
  rw [Function.update_of_ne hne]

open Classical in
theorem Section34CompactExterior.update_of_subset_union
    {tgtV : Section34CompactVertexIndex K K' → Set E3}
    {fbl : Section34CompactSimplexIndex K 3 → Set E3}
    (hext : Section34CompactExterior K K' h tgtV fbl) {s : Section34CompactSimplexIndex K 3}
    {F Z : Set E3} (hFZ : F ⊆ fbl s ∪ Z)
    (hr : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      ∃ (r : E3 → E3) (Y B : Set E3), IsCompact Y ∧ Bornology.IsBounded B ∧
        frontier Y ⊆ section34CompactTetraObstacle tgtV fbl t ∧
        ContinuousOn r ((section34CompactTetraObstacle tgtV fbl t)ᶜ \ Y) ∧
        MapsTo r ((section34CompactTetraObstacle tgtV fbl t)ᶜ \ Y)
          (section34CompactTetraObstacle tgtV fbl t ∪ Z)ᶜ ∧
        (∀ x ∉ B, r x = x) ∧
        ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
          ∀ y ∈ h '' (w.1 : Set E3), r y = y) :
    Section34CompactExterior K K' h tgtV (Function.update fbl s F) := by
  intro t w hw y hy
  have hunb := hext t w hw y hy
  by_cases hst : Section34Incident s.1 t.1
  · obtain ⟨r, Y, B, hY, hB, hYfr, hrc, hrm, hrB, hrw⟩ := hr t hst
    have hyO : y ∈ (section34CompactTetraObstacle tgtV fbl t)ᶜ := by
      by_contra hyO
      rw [connectedComponentIn_eq_empty hyO] at hunb
      exact hunb Bornology.isBounded_empty
    have hCO : connectedComponentIn (section34CompactTetraObstacle tgtV fbl t)ᶜ y ⊆
        (section34CompactTetraObstacle tgtV fbl t)ᶜ := connectedComponentIn_subset _ _
    have hCpc : IsPreconnected
        (connectedComponentIn (section34CompactTetraObstacle tgtV fbl t)ᶜ y) :=
      isPreconnected_connectedComponentIn
    have hCY : connectedComponentIn (section34CompactTetraObstacle tgtV fbl t)ᶜ y ⊆ Yᶜ := by
      have hdis : Disjoint (connectedComponentIn (section34CompactTetraObstacle tgtV fbl t)ᶜ y)
          (frontier Y) := Set.disjoint_left.mpr fun x hx hxY => hCO hx (hYfr hxY)
      rcases subset_interior_or_subset_compl_of_disjoint_frontier hY.isClosed hCpc hdis with
        h1 | h1
      · exact absurd (hY.isBounded.subset (h1.trans interior_subset)) hunb
      · exact h1
    have hCdom : connectedComponentIn (section34CompactTetraObstacle tgtV fbl t)ᶜ y ⊆
        (section34CompactTetraObstacle tgtV fbl t)ᶜ \ Y := fun x hx => ⟨hCO hx, hCY hx⟩
    have hobs := section34CompactTetraObstacle_update_subset (tgtV := tgtV) hFZ t
    have hsub : r '' connectedComponentIn (section34CompactTetraObstacle tgtV fbl t)ᶜ y ⊆
        (section34CompactTetraObstacle tgtV (Function.update fbl s F) t)ᶜ := by
      rintro _ ⟨x, hx, rfl⟩ hxo
      exact hrm (hCdom hx) (hobs hxo)
    have hyimg : y ∈ r '' connectedComponentIn (section34CompactTetraObstacle tgtV fbl t)ᶜ y :=
      ⟨y, mem_connectedComponentIn hyO, hrw w hw y hy⟩
    have hsubC := (hCpc.image r (hrc.mono hCdom)).subset_connectedComponentIn hyimg hsub
    intro hbdd
    apply hunb
    refine ((hbdd.subset hsubC).union hB).subset fun x hx => ?_
    by_cases hxB : x ∈ B
    · exact Or.inr hxB
    · exact Or.inl ⟨x, hx, hrB x hxB⟩
  · change ¬ Bornology.IsBounded (connectedComponentIn
      (section34CompactTetraObstacle tgtV (Function.update fbl s F) t)ᶜ y)
    rw [section34CompactTetraObstacle_update_of_not_incident F hst]
    exact hunb

end Exterior

section Invariants

variable {K K' : Geometry.SimplicialComplex ℝ E3} {h : E3 → E3} {H : Finset E3 → Set E3}

open Classical in
theorem section34CompactFaceBallInvariants_update_of_overlap
    {tgtV : Section34CompactVertexIndex K K' → Set E3}
    {tgtEBd : Section34CompactEdgeIndex K K' → Set E3}
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl fblBd)
    {s : Section34CompactSimplexIndex K 3} {F Fb Z : Set E3} (hF : IsPLCellOn 3 F Fb)
    (hrim : h '' section34CompactSimplexRim s.1 ⊆ interior F) (hFZ : F ⊆ fbl s ∪ Z)
    (hZV : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 s.1 →
      Disjoint Z (tgtV w))
    (hZs : ∀ s', s' ≠ s → Z ∩ fbl s' ⊆ interior (⋃ w, tgtV w))
    (hZH : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      Z ⊆ interior (H t.1))
    (hr : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      ∃ (r : E3 → E3) (Y B : Set E3), IsCompact Y ∧ Bornology.IsBounded B ∧
        frontier Y ⊆ section34CompactTetraObstacle tgtV fbl t ∧
        ContinuousOn r ((section34CompactTetraObstacle tgtV fbl t)ᶜ \ Y) ∧
        MapsTo r ((section34CompactTetraObstacle tgtV fbl t)ᶜ \ Y)
          (section34CompactTetraObstacle tgtV fbl t ∪ Z)ᶜ ∧
        (∀ x ∉ B, r x = x) ∧
        ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
          ∀ y ∈ h '' (w.1 : Set E3), r y = y)
    (h5 : ∀ y ∈ Fb ∩ frontier (⋃ w, tgtV w), HasPLCrossingAt Fb (frontier (⋃ w, tgtV w)) y)
    (h6 : ∀ (e : Section34CompactEdgeIndex K K'), ∀ y ∈ Fb ∩ tgtEBd e,
      HasPLSurfaceCurveCrossingAt (frontier (⋃ w, tgtV w)) (Fb ∩ frontier (⋃ w, tgtV w))
        (tgtEBd e) y)
    (h7 : CarriesIntegralFirstHomologyOnto (Fb ∩ frontier (section34CompactFaceTorus tgtV s))
      (section34CompactFaceTorus tgtV s))
    (h8 : (Fb ∩ ⋃ e : Section34CompactEdgeIndex K K', tgtEBd e).Finite)
    (h9 : ((fun y => connectedComponentIn (Fb ∩ frontier (⋃ w, tgtV w)) y) ''
      (Fb ∩ frontier (⋃ w, tgtV w))).Finite) :
    Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd (Function.update fbl s F)
      (Function.update fblBd s Fb) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11⟩ := hinv
  have hFs : ∀ s', s' ≠ s → F ∩ fbl s' ⊆ interior (⋃ w, tgtV w) := by
    rintro s' hs' x ⟨hxF, hx'⟩
    rcases hFZ hxF with hx | hx
    · exact hc4 s s' (Ne.symm hs') ⟨hx, hx'⟩
    · exact hZs s' hs' ⟨hx, hx'⟩
  refine ⟨fun s' => ?_, fun s' => ?_, fun s' w hw => ?_, fun s₁ s₂ hne => ?_, fun s' => ?_,
    fun s' e => ?_, fun s' => ?_, fun s' => ?_, fun s' => ?_, fun s' t hst => ?_,
    hc11.update_of_subset_union hFZ hr⟩
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using hF
    · simpa only [Function.update_of_ne hs] using hc1 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using hrim
    · simpa only [Function.update_of_ne hs] using hc2 s'
  · by_cases hs : s' = s
    · have hw' : ¬ Section34Incident w.1 s.1 := by rwa [hs] at hw
      rw [hs, Function.update_self]
      refine eq_empty_iff_forall_notMem.mpr fun x ⟨hxF, hxw⟩ => ?_
      rcases hFZ hxF with hx | hx
      · have hmem : x ∈ fbl s ∩ tgtV w := ⟨hx, hxw⟩
        rw [hc3 s w hw'] at hmem
        exact hmem
      · exact Set.disjoint_left.mp (hZV w hw') hx hxw
    · rw [Function.update_of_ne hs]
      exact hc3 s' w hw
  · by_cases hs₁ : s₁ = s
    · have hs₂ : s₂ ≠ s := fun h => hne (hs₁.trans h.symm)
      rw [hs₁, Function.update_self, Function.update_of_ne hs₂]
      exact hFs s₂ hs₂
    · by_cases hs₂ : s₂ = s
      · rw [hs₂, Function.update_self, Function.update_of_ne hs₁, inter_comm]
        exact hFs s₁ hs₁
      · rw [Function.update_of_ne hs₁, Function.update_of_ne hs₂]
        exact hc4 s₁ s₂ hne
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h5
    · simpa only [Function.update_of_ne hs] using hc5 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h6 e
    · simpa only [Function.update_of_ne hs] using hc6 s' e
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h7
    · simpa only [Function.update_of_ne hs] using hc7 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [Function.update_self] using h8
    · simpa only [Function.update_of_ne hs] using hc8 s'
  · rcases eq_or_ne s' s with rfl | hs
    · simpa only [section34CompactTraceComponents, Function.update_self] using h9
    · simpa only [section34CompactTraceComponents, Function.update_of_ne hs] using hc9 s'
  · rcases eq_or_ne s' s with rfl | hs
    · rw [Function.update_self]
      intro x hx
      rcases hFZ hx with hx' | hx'
      · exact hc10 _ t hst hx'
      · exact hZH t hst hx'
    · rw [Function.update_of_ne hs]
      exact hc10 s' t hst

theorem section34CompactFaceBall_fields_of_inter_eq
    {tgtV : Section34CompactVertexIndex K K' → Set E3}
    {tgtEBd : Section34CompactEdgeIndex K K' → Set E3}
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl fblBd)
    {s : Section34CompactSimplexIndex K 3} {F Fb OM : Set E3} (hOM : IsOpen OM)
    (hF : IsClosed F) (hFbO : Fb ∩ OM = fblBd s ∩ OM)
    (hZO : Fb ∩ frontier (⋃ w, tgtV w) ⊆ OM) (hEO : ∀ e, Fb ∩ tgtEBd e ⊆ OM)
    (hZF : Fb ∩ frontier (⋃ w, tgtV w) = fblBd s ∩ frontier (⋃ w, tgtV w) ∩ F)
    {y₀ : E3} (hy₀ : y₀ ∈ fblBd s ∩ frontier (⋃ w, tgtV w)) (hy₀F : y₀ ∉ F) :
    (∀ y ∈ Fb ∩ frontier (⋃ w, tgtV w), HasPLCrossingAt Fb (frontier (⋃ w, tgtV w)) y) ∧
    (∀ e : Section34CompactEdgeIndex K K', ∀ y ∈ Fb ∩ tgtEBd e,
      HasPLSurfaceCurveCrossingAt (frontier (⋃ w, tgtV w)) (Fb ∩ frontier (⋃ w, tgtV w))
        (tgtEBd e) y) ∧
    (Fb ∩ ⋃ e : Section34CompactEdgeIndex K K', tgtEBd e).Finite ∧
    ((fun y => connectedComponentIn (Fb ∩ frontier (⋃ w, tgtV w)) y) ''
      (Fb ∩ frontier (⋃ w, tgtV w))).Finite ∧
    ((fun y => connectedComponentIn (Fb ∩ frontier (⋃ w, tgtV w)) y) ''
      (Fb ∩ frontier (⋃ w, tgtV w))).ncard + 1 ≤
      ((fun y => connectedComponentIn (fblBd s ∩ frontier (⋃ w, tgtV w)) y) ''
        (fblBd s ∩ frontier (⋃ w, tgtV w))).ncard ∧
    (Fb ∩ ⋃ e : Section34CompactEdgeIndex K K', tgtEBd e).ncard ≤
      (fblBd s ∩ ⋃ e : Section34CompactEdgeIndex K K', tgtEBd e).ncard := by
  obtain ⟨-, -, -, -, hf5, hf6, -, hf8, hf9, -, -⟩ := hinv
  have hloc : ∀ z ∈ OM, z ∈ fblBd s ↔ z ∈ Fb := by
    intro z hz
    constructor
    · intro h1
      have h2 : z ∈ fblBd s ∩ OM := ⟨h1, hz⟩
      rw [← hFbO] at h2
      exact h2.1
    · intro h1
      have h2 : z ∈ Fb ∩ OM := ⟨h1, hz⟩
      rw [hFbO] at h2
      exact h2.1
  have hZ'O : Fb ∩ frontier (⋃ w, tgtV w) = fblBd s ∩ frontier (⋃ w, tgtV w) ∩ OM := by
    ext y
    constructor
    · intro hy
      exact ⟨⟨(hloc y (hZO hy)).mpr hy.1, hy.2⟩, hZO hy⟩
    · rintro ⟨⟨hy, hySg⟩, hyOM⟩
      exact ⟨(hloc y hyOM).mp hy, hySg⟩
  have hy₀' : y₀ ∉ Fb ∩ frontier (⋃ w, tgtV w) := fun hy => by
    rw [hZF] at hy
    exact hy₀F hy.2
  have hsub := image_connectedComponentIn_subset_diff hOM hF hZ'O hZF hy₀ hy₀'
  have h8sub : Fb ∩ ⋃ e : Section34CompactEdgeIndex K K', tgtEBd e ⊆
      fblBd s ∩ ⋃ e : Section34CompactEdgeIndex K K', tgtEBd e := by
    rintro y ⟨hy, hyE⟩
    obtain ⟨e, hye⟩ := mem_iUnion.mp hyE
    exact ⟨(hloc y (hEO e ⟨hy, hye⟩)).mpr hy, hyE⟩
  refine ⟨fun y hy => ?_, fun e y hy => ?_, (hf8 s).subset h8sub,
    (hf9 s).subset (hsub.trans sdiff_subset),
    ncard_image_connectedComponentIn_add_one_le hOM hF hZ'O hZF hy₀ hy₀' (hf9 s),
    Set.ncard_le_ncard h8sub (hf8 s)⟩
  · have hyOM := hZO hy
    refine (hf5 s y ⟨(hloc y hyOM).mpr hy.1, hy.2⟩).congr ?_
      (Filter.Eventually.of_forall fun _ => Iff.rfl)
    filter_upwards [hOM.mem_nhds hyOM] with z hz using hloc z hz
  · have hyOM := hEO e hy
    have hc : HasPLCurveCrossingOnAt (frontier (⋃ w, tgtV w))
        (fblBd s ∩ frontier (⋃ w, tgtV w)) (tgtEBd e) y :=
      hf6 s e y ⟨(hloc y hyOM).mpr hy.1, hy.2⟩
    change HasPLCurveCrossingOnAt _ _ _ _
    refine hc.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_
      (Filter.Eventually.of_forall fun _ => Iff.rfl)
    filter_upwards [hOM.mem_nhds hyOM] with z hz
    exact and_congr (hloc z hz) Iff.rfl

theorem exists_compactCompression_of_ball
    {tgtV : Section34CompactVertexIndex K K' → Set E3}
    {tgtEBd : Section34CompactEdgeIndex K K' → Set E3}
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl fblBd)
    (s : Section34CompactSimplexIndex K 3) {O₀ : Set E3} (hfO₀ : fbl s ⊆ O₀)
    (hSgO₀ : frontier (⋃ w, tgtV w) ∩ O₀ = frontier (section34CompactFaceTorus tgtV s) ∩ O₀)
    {G Z Oc Sel : Set E3} (hG : IsPLBall 3 G) (hGO₀ : G ⊆ O₀)
    (hrim : h '' section34CompactSimplexRim s.1 ⊆ interior G) (hGZ : G ⊆ fbl s ∪ Z)
    (hZV : ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 s.1 →
      Disjoint Z (tgtV w))
    (hZs : ∀ s', s' ≠ s → Z ∩ fbl s' ⊆ interior (⋃ w, tgtV w))
    (hZH : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      Z ⊆ interior (H t.1))
    (hr : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      ∃ (r : E3 → E3) (Y B : Set E3), IsCompact Y ∧ Bornology.IsBounded B ∧
        frontier Y ⊆ section34CompactTetraObstacle tgtV fbl t ∧
        ContinuousOn r ((section34CompactTetraObstacle tgtV fbl t)ᶜ \ Y) ∧
        MapsTo r ((section34CompactTetraObstacle tgtV fbl t)ᶜ \ Y)
          (section34CompactTetraObstacle tgtV fbl t ∪ Z)ᶜ ∧
        (∀ x ∉ B, r x = x) ∧
        ∀ w : Section34CompactVertexIndex K K', ¬ Section34Incident w.1 t.1 →
          ∀ y ∈ h '' (w.1 : Set E3), r y = y)
    (hOc : IsOpen Oc) (hfrO : frontier G ∩ Oc = fblBd s ∩ Oc)
    (hk2 : frontier G ∩ frontier (section34CompactFaceTorus tgtV s) ⊆ Oc)
    (hk4 : ∀ e : Section34CompactEdgeIndex K K', frontier G ∩ tgtEBd e ⊆ Oc)
    (hk3 : frontier G ∩ frontier (section34CompactFaceTorus tgtV s) =
      fblBd s ∩ frontier (section34CompactFaceTorus tgtV s) ∩ Sel)
    (hSel : IsClosed Sel) {y₀ : E3} (hy₀ : y₀ ∈ fblBd s ∩ frontier (⋃ w, tgtV w))
    (hy₀S : y₀ ∉ Sel)
    (h7 : CarriesIntegralFirstHomologyOnto
      (frontier G ∩ frontier (section34CompactFaceTorus tgtV s))
      (section34CompactFaceTorus tgtV s)) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set E3,
      Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34CompactTraceCount tgtV fblBd' s + 1 ≤ section34CompactTraceCount tgtV fblBd s ∧
      section34CompactCrossingCount tgtEBd fblBd' s ≤
        section34CompactCrossingCount tgtEBd fblBd s := by
  classical
  obtain ⟨hfcell, -⟩ := id hinv
  have hfbs : fblBd s ⊆ fbl s := (hfcell s).boundary_subset
  have hGc : IsClosed G := hG.isPolyhedron.isClosed
  have hfrGG : frontier G ⊆ G := hGc.frontier_subset
  have hSgT : ∀ y ∈ O₀, (y ∈ frontier (⋃ w, tgtV w) ↔
      y ∈ frontier (section34CompactFaceTorus tgtV s)) := by
    intro y hy
    constructor
    · intro h1
      have h2 : y ∈ frontier (⋃ w, tgtV w) ∩ O₀ := ⟨h1, hy⟩
      rw [hSgO₀] at h2
      exact h2.1
    · intro h1
      have h2 : y ∈ frontier (section34CompactFaceTorus tgtV s) ∩ O₀ := ⟨h1, hy⟩
      rw [← hSgO₀] at h2
      exact h2.1
  have hZO : frontier G ∩ frontier (⋃ w, tgtV w) ⊆ Oc := fun y hy =>
    hk2 ⟨hy.1, (hSgT y (hGO₀ (hfrGG hy.1))).mp hy.2⟩
  have hZF : frontier G ∩ frontier (⋃ w, tgtV w) =
      fblBd s ∩ frontier (⋃ w, tgtV w) ∩ Sel := by
    ext y
    constructor
    · rintro ⟨hy, hySg⟩
      have hx : y ∈ frontier G ∩ frontier (section34CompactFaceTorus tgtV s) :=
        ⟨hy, (hSgT y (hGO₀ (hfrGG hy))).mp hySg⟩
      rw [hk3] at hx
      exact ⟨⟨hx.1.1, hySg⟩, hx.2⟩
    · rintro ⟨⟨hy, hySg⟩, hyS⟩
      have hx : y ∈ fblBd s ∩ frontier (section34CompactFaceTorus tgtV s) ∩ Sel :=
        ⟨⟨hy, (hSgT y (hfO₀ (hfbs hy))).mp hySg⟩, hyS⟩
      rw [← hk3] at hx
      exact ⟨hx.1, hySg⟩
  obtain ⟨h5, h6, h8, h9, hcount, hpcount⟩ := section34CompactFaceBall_fields_of_inter_eq hinv hOc
    hSel hfrO hZO hk4 hZF hy₀ hy₀S
  refine ⟨Function.update fbl s G, Function.update fblBd s (frontier G),
    section34CompactFaceBallInvariants_update_of_overlap hinv hG.isPLCellOn_frontier hrim hGZ
      hZV hZs hZH hr h5 h6 h7 h8 h9,
    fun s' hs' => ⟨Function.update_of_ne hs' _ _, Function.update_of_ne hs' _ _⟩, ?_, ?_⟩
  · simp only [section34CompactTraceCount, section34CompactTraceComponents, Function.update_self]
    exact hcount
  · simp only [section34CompactCrossingCount, Function.update_self]
    exact hpcount

end Invariants

end DifferentialGeometry.Topology.PiecewiseLinear
