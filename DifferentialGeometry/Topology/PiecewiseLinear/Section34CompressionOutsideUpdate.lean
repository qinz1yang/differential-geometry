/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionOutsideTools

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Chart

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η ψ : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

theorem exists_chart_section34FaceBall_tetra (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁)
    {fbl : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hext : Section34Exterior 𝒦 𝒦' h H (section34VertexBallImage src f₁) fbl)
    (s : Section34SimplexIndex 𝒦 3)
    (hfV : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 s.1 →
      fbl s ∩ section34VertexBallImage src f₁ w = ∅) :
    ∃ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 ∧
    ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, H t.1 ⊆ c.source ∧ fbl s ⊆ c.source ∧
      section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source ∧
      IsCompact (section34FaceTorus (section34VertexBallImage src f₁) s) ∧
      ∃ O₀ : Set M₂, O₀ = interior (H t.1) \ ⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
        (section34VertexBallImage src f₁ w' ∩ H t.1).Nonempty ∧ ¬ Section34Incident w'.1 s.1},
        section34VertexBallImage src f₁ w' ∧ IsOpen O₀ ∧ fbl s ⊆ O₀ ∧
        frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ O₀ =
          frontier (section34FaceTorus (section34VertexBallImage src f₁) s) ∩ O₀ := by
  obtain ⟨hext1, -, -⟩ := hext
  obtain ⟨-, hsubdiv, -, hcell, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hcof⟩ := id hcut
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := id hgraph
  obtain ⟨-, -, -, -, -, hchart⟩ := id hctrl
  obtain ⟨t, hst⟩ := hcof s
  obtain ⟨c, hc, hHc⟩ := hchart t.1 t.2.1
  have hNV : ∀ v : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall v) ⊆ section34CutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (Section34Label.vertexBall v)) v
  have hVcell : ∀ w' : Section34VertexIndex 𝒦 𝒦',
      IsPLCellOn 3 (section34VertexBallImage src f₁ w') (section34VertexBallImage srcBd f₁ w') :=
    fun w' => (hcell (.vertexBall w')).image
      (hf₁.mono_of_isPLCellOn (hcell (.vertexBall w')) (hNV w'))
  have hVt : ∀ w' : Section34VertexIndex 𝒦 𝒦', Section34Incident w'.1 s.1 →
      section34VertexBallImage src f₁ w' ⊆ interior (H t.1) := fun w' hw =>
    image_vertexBall_subset_interior_of_incident hh hcut hctrl hgraph w' t.2.1
      (Subset.trans hw (convexHull_min hst (convex_convexHull ℝ _)))
  have hTeq : section34FaceTorus (section34VertexBallImage src f₁) s =
      ⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' | Section34Incident w'.1 s.1},
        section34VertexBallImage src f₁ w' := by
    apply Subset.antisymm
    · intro z hz
      obtain ⟨a, ha, hza⟩ := mem_iUnion₂.mp hz
      have hia : Section34Incident a.1.2.1 s.1 := by
        rw [← ha]
        exact a.2
      exact mem_iUnion₂.mpr ⟨a.1.2, hia, hza⟩
    · exact iUnion₂_subset fun w' hw' z hz => mem_iUnion₂.mpr ⟨⟨(s, w'), hw'⟩, rfl, hz⟩
  have hfsH : fbl s ⊆ interior (H t.1) := by
    refine Subset.trans ?_ (hext1 t)
    unfold section34TetraObstacle
    exact subset_union_of_subset_right
      (subset_iUnion₂ (s := fun s' (_ : Section34Incident s'.1 t.1) => fbl s') s hst) _
  have hTH : section34FaceTorus (section34VertexBallImage src f₁) s ⊆ interior (H t.1) := by
    rw [hTeq]
    exact iUnion₂_subset fun w' hw' => hVt w' hw'
  have hQc : IsClosed (⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
      (section34VertexBallImage src f₁ w' ∩ H t.1).Nonempty ∧ ¬ Section34Incident w'.1 s.1},
      section34VertexBallImage src f₁ w') :=
    ((finite_setOf_vertexBallImage_inter_nonempty hctrl hgraph t.2.1).subset
      fun w' hw' => hw'.1).isClosed_biUnion fun w' _ => (hVcell w').isCompact.isClosed
  have hO₀o := isOpen_interior (s := H t.1) |>.sdiff hQc
  have hUO₀ : ∀ Y : Set M₂, Y = interior (H t.1) \ ⋃ w' ∈ {w' : Section34VertexIndex 𝒦 𝒦' |
      (section34VertexBallImage src f₁ w' ∩ H t.1).Nonempty ∧ ¬ Section34Incident w'.1 s.1},
      section34VertexBallImage src f₁ w' →
      (⋃ w', section34VertexBallImage src f₁ w') ∩ Y =
        section34FaceTorus (section34VertexBallImage src f₁) s ∩ Y := by
    rintro Y rfl
    apply Subset.antisymm
    · rintro z ⟨hz, hzH, hzQ⟩
      obtain ⟨w', hzw'⟩ := mem_iUnion.mp hz
      by_cases hw' : Section34Incident w'.1 s.1
      · exact ⟨mem_iUnion₂.mpr ⟨⟨(s, w'), hw'⟩, rfl, hzw'⟩, hzH, hzQ⟩
      · exact absurd (mem_iUnion₂.mpr ⟨w', ⟨⟨z, hzw', interior_subset hzH⟩, hw'⟩, hzw'⟩) hzQ
    · rintro z ⟨hz, hzO⟩
      obtain ⟨a, -, hza⟩ := mem_iUnion₂.mp hz
      exact ⟨mem_iUnion.mpr ⟨a.1.2, hza⟩, hzO⟩
  refine ⟨t, hst, c, hc, hHc, hfsH.trans (interior_subset.trans hHc),
    hTH.trans (interior_subset.trans hHc), ?_, _, rfl, hO₀o, ?_, ?_⟩
  · rw [hTeq]
    exact (finite_setOf_section34Incident_graphIndex hsubdiv _ 1 s.2.1).isCompact_biUnion
      fun w' _ => (hVcell w').isCompact
  · intro z hz
    refine ⟨hfsH hz, fun hzQ => ?_⟩
    obtain ⟨w', ⟨-, hw'⟩, hzw'⟩ := mem_iUnion₂.mp hzQ
    have hmem : z ∈ fbl s ∩ section34VertexBallImage src f₁ w' := ⟨hz, hzw'⟩
    rw [hfV w' hw'] at hmem
    exact hmem
  · rw [← frontier_inter_open_inter hO₀o, hUO₀ _ rfl, frontier_inter_open_inter hO₀o]

end Chart

section Invariants

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}

open Classical in
theorem section34FaceBallInvariants_update_of_overlap
    {tgtV : Section34VertexIndex 𝒦 𝒦' → Set M₂} {tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
    {fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂}
    (hinv : Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd fbl fblBd)
    {s : Section34SimplexIndex 𝒦 3} {F Fb Z : Set M₂} (hF : IsPLCellOn 3 F Fb)
    (hrim : h '' simplexRim 𝒦 s.1 ⊆ interior F) (hFZ : F ⊆ fbl s ∪ Z)
    (hZV : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 s.1 → Disjoint Z (tgtV w))
    (hZs : ∀ s', s' ≠ s → Z ∩ fbl s' ⊆ interior (⋃ w, tgtV w))
    (hZH : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 → Z ⊆ interior (H t.1))
    (hr : ∀ t : Section34SimplexIndex 𝒦 4, Section34Incident s.1 t.1 → ∃ r : M₂ → M₂,
      ContinuousOn r (H t.1 \ section34TetraObstacle tgtV fbl t) ∧
      MapsTo r (H t.1 \ section34TetraObstacle tgtV fbl t)
        (H t.1 \ (section34TetraObstacle tgtV fbl t ∪ Z)) ∧
      (∀ z ∈ frontier (H t.1), r z = z) ∧
      ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 t.1 →
        ∀ y ∈ h '' simplexBody 𝒦' w.1, r y = y)
    (h5 : ∀ y ∈ Fb ∩ frontier (⋃ w, tgtV w), ∃ c ∈ (plGroupoid 3).maximalAtlas M₂,
      y ∈ c.source ∧ HasPLCrossingAt (c '' (Fb ∩ c.source))
        (c '' (frontier (⋃ w, tgtV w) ∩ c.source)) (c y))
    (h6 : ∀ e : Section34EdgeIndex 𝒦 𝒦', ∀ y ∈ Fb ∩ tgtEBd e,
      ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
        HasPLCurveCrossingOnAt (c '' (frontier (⋃ w, tgtV w) ∩ c.source))
          (c '' (Fb ∩ frontier (⋃ w, tgtV w) ∩ c.source)) (c '' (tgtEBd e ∩ c.source)) (c y))
    (h7 : CarriesFirstHomologyOnto (Fb ∩ frontier (section34FaceTorus tgtV s))
      (section34FaceTorus tgtV s))
    (h8 : (Fb ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', tgtEBd e).Finite)
    (h9 : ((fun y => connectedComponentIn (Fb ∩ frontier (⋃ w, tgtV w)) y) ''
      (Fb ∩ frontier (⋃ w, tgtV w))).Finite) :
    Section34FaceBallInvariants 𝒦 𝒦' h H tgtV tgtEBd (Function.update fbl s F)
      (Function.update fblBd s Fb) := by
  classical
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10⟩ := hinv
  have hFs : ∀ s', s' ≠ s → F ∩ fbl s' ⊆ interior (⋃ w, tgtV w) := by
    rintro s' hs' x ⟨hxF, hx'⟩
    rcases hFZ hxF with hx | hx
    · exact hc4 s s' (Ne.symm hs') ⟨hx, hx'⟩
    · exact hZs s' hs' ⟨hx, hx'⟩
  refine ⟨fun s' => ?_, fun s' => ?_, fun s' w hw => ?_, fun s₁ s₂ hne => ?_, fun s' => ?_,
    fun s' e => ?_, fun s' => ?_, fun s' => ?_, fun s' => ?_,
    hc10.update_of_subset_union hFZ hZH hr⟩
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
    · simpa only [section34TraceComponents, Function.update_self] using h9
    · simpa only [section34TraceComponents, Function.update_of_ne hs] using hc9 s'

end Invariants

end DifferentialGeometry.Topology.PiecewiseLinear
