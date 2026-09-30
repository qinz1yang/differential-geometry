/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homeomorph.SubsetImage
import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.ChartBallGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.ChartImagePLCell
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ExteriorComponent
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallNeighborhoods
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceTorusHomology
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SplitDiskIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.SimplexBoundaryImage
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCurveTriangulation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem eq_or_eq_of_card_eq_one_of_subset_union {α : Type*} {u w w' : Finset α}
    (hu : u.card = 1) (hw : w.card = 1) (hw' : w'.card = 1)
    (h : (u : Set α) ⊆ (w : Set α) ∪ (w' : Set α)) : u = w ∨ u = w' := by
  obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hu
  obtain ⟨q, rfl⟩ := Finset.card_eq_one.mp hw
  obtain ⟨q', rfl⟩ := Finset.card_eq_one.mp hw'
  have hp := h (Finset.mem_coe.mpr (Finset.mem_singleton_self p))
  simp only [Finset.coe_singleton, mem_union, mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

section FaceBall

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U W : Set M₁} {h : M₁ → M₂} {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U} {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

theorem exists_section34FaceBall_of_neighborhood (hh : IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd) (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U W h ψ H 𝒦 𝒦' src cr f₁) (s : Section34SimplexIndex 𝒦 3)
    {t : Section34SimplexIndex 𝒦 4} (hst : Section34Incident s.1 t.1) {Wn : Set M₂}
    (hWo : IsOpen Wn) (hWt : Wn ⊆ interior (H t.1))
    (hWV : ∀ w : Section34VertexIndex 𝒦 𝒦', ¬ Section34Incident w.1 s.1 →
      Wn ∩ section34VertexBallImage src f₁ w = ∅)
    {C Cb : Set M₂} (hC : IsPLCellOn 3 C Cb) (hbodyC : h '' simplexBody 𝒦 s.1 ⊆ interior C)
    (hCW : C ⊆ Wn) {C' : Set M₂} (hC'c : IsCompact C')
    (hC'1 : Subsingleton (integralSingularHomology 1 C')) (hRC' : h '' simplexRim 𝒦 s.1 ⊆ C')
    (hWC' : Disjoint Wn
      (C' \ interior (section34FaceTorus (section34VertexBallImage src f₁) s))) :
    ∃ F Fb : Set M₂, IsPLCellOn 3 F Fb ∧ h '' simplexRim 𝒦 s.1 ⊆ interior F ∧ F ⊆ Wn ∧
      (∀ y ∈ Fb ∩ frontier (⋃ w, section34VertexBallImage src f₁ w),
        ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
          HasPLCrossingAt (c '' (Fb ∩ c.source))
            (c '' (frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ c.source)) (c y)) ∧
      (∀ e : Section34EdgeIndex 𝒦 𝒦', ∀ y ∈ Fb ∩ section34SplitDiskImage srcBd f₁ e,
        ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
          HasPLCurveCrossingOnAt
            (c '' (frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ c.source))
            (c '' (Fb ∩ frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ c.source))
            (c '' (section34SplitDiskImage srcBd f₁ e ∩ c.source)) (c y)) ∧
      CarriesFirstHomologyOnto
        (Fb ∩ frontier (section34FaceTorus (section34VertexBallImage src f₁) s))
        (section34FaceTorus (section34VertexBallImage src f₁) s) ∧
      (Fb ∩ ⋃ e : Section34EdgeIndex 𝒦 𝒦', section34SplitDiskImage srcBd f₁ e).Finite ∧
      ((fun y => connectedComponentIn
          (Fb ∩ frontier (⋃ w, section34VertexBallImage src f₁ w)) y) ''
        (Fb ∩ frontier (⋃ w, section34VertexBallImage src f₁ w))).Finite := by
  classical
  obtain ⟨-, hsubdiv, -, hcell, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hvertexEdge,
    hends, -, -⟩ := id hcut
  obtain ⟨-, -, hf₁, -, -, -, -, -, -, -, -, -, -, -⟩ := id hgraph
  obtain ⟨-, -, -, -, -, hchart⟩ := id hctrl
  obtain ⟨c, hc, hHc⟩ := hchart t.1 t.2.1
  have hWc : Wn ⊆ c.source := hWt.trans (interior_subset.trans hHc)
  have hNV : ∀ v : Section34VertexIndex 𝒦 𝒦',
      src (.vertexBall v) ⊆ section34CutNeighborhood src :=
    fun v => subset_iUnion (fun v => src (Section34Label.vertexBall v)) v
  have hinc : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 →
      Section34Incident w.1 t.1 :=
    fun w hw => Subset.trans hw (convexHull_min hst (convex_convexHull ℝ _))
  have hVc : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 →
      section34VertexBallImage src f₁ w ⊆ c.source := fun w hw =>
    (image_vertexBall_subset_interior_of_incident hh hcut hctrl hgraph w t.2.1
      (hinc w hw)).trans (interior_subset.trans hHc)
  have hsK : convexHull ℝ (s.1 : Set Ea) ⊆ 𝒦'.complex.space := by
    rw [hsubdiv.space_eq]
    exact 𝒦.complex.convexHull_subset_space s.2.1
  have hfinFaces := 𝒦'.finite_faces_inter_of_isCompact
    (s.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)) hsK
  obtain ⟨I, hI⟩ : ∃ I : Set (Section34VertexIndex 𝒦 𝒦'),
      I = {w | Section34Incident w.1 s.1} := ⟨_, rfl⟩
  have hIm : ∀ w, w ∈ I ↔ Section34Incident w.1 s.1 := fun w => by rw [hI]; exact Iff.rfl
  obtain ⟨E', hE'⟩ : ∃ E' : Set (Section34EdgeIndex 𝒦 𝒦'),
      E' = {e | Section34Incident e.1 s.1} := ⟨_, rfl⟩
  have hEm : ∀ e, e ∈ E' ↔ Section34Incident e.1 s.1 := fun e => by rw [hE']; exact Iff.rfl
  have hIfin : I.Finite := by
    refine Set.Finite.of_finite_image (f := fun w : Section34VertexIndex 𝒦 𝒦' => w.1)
      (hfinFaces.subset ?_) Subtype.val_injective.injOn
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨q, hq⟩ := 𝒦'.complex.nonempty_of_mem_faces w.2.1
    exact ⟨w.2.1, q, subset_convexHull ℝ _ (Finset.mem_coe.mpr hq),
      (hIm w).mp hw (Finset.mem_coe.mpr hq)⟩
  have hEfin : E'.Finite := by
    refine Set.Finite.of_finite_image (f := fun e : Section34EdgeIndex 𝒦 𝒦' => e.1)
      (hfinFaces.subset ?_) Subtype.val_injective.injOn
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨q, hq⟩ := 𝒦'.complex.nonempty_of_mem_faces e.2.1
    exact ⟨e.2.1, q, subset_convexHull ℝ _ (Finset.mem_coe.mpr hq),
      (hEm e).mp he (Finset.mem_coe.mpr hq)⟩
  have : Finite I := hIfin.to_subtype
  have : Finite E' := hEfin.to_subtype
  have hTs : section34FaceTorus (section34VertexBallImage src f₁) s =
      ⋃ i : I, section34VertexBallImage src f₁ i.1 := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp hy
      have hia : Section34Incident a.1.2.1 s.1 := by
        rw [← ha]
        exact a.2
      exact mem_iUnion.mpr ⟨⟨a.1.2, (hIm _).mpr hia⟩, hya⟩
    · intro y hy
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
      exact mem_iUnion₂.mpr ⟨⟨(s, i.1), (hIm _).mp i.2⟩, rfl, hyi⟩
  have hVcell : ∀ w : Section34VertexIndex 𝒦 𝒦',
      IsPLCellOn 3 (section34VertexBallImage src f₁ w) (f₁ '' srcBd (.vertexBall w)) := fun w =>
    (hcell (.vertexBall w)).image (hf₁.mono_of_isPLCellOn (hcell (.vertexBall w)) (hNV w))
  have hDN : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      src (.splitDisk e) ⊆ section34CutNeighborhood src := by
    intro e
    obtain ⟨w, _, -, -, he⟩ := hends e
    rw [he]
    exact inter_subset_left.trans (hNV w)
  have hDcell : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      IsPLCellOn 2 (f₁ '' src (.splitDisk e)) (f₁ '' srcBd (.splitDisk e)) := fun e =>
    (hcell (.splitDisk e)).image (hf₁.mono_of_isPLCellOn (hcell (.splitDisk e)) (hDN e))
  have hBall : ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 →
      IsPLBall 3 (c '' section34VertexBallImage src f₁ w) ∧
        c '' (f₁ '' srcBd (.vertexBall w)) = frontier (c '' section34VertexBallImage src f₁ w) :=
    fun w hw => (hVcell w).isPLBall_image_chart hc (hVc w hw)
  have hinter2 : ∀ w w' : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 →
      Section34Incident w'.1 s.1 →
      c '' section34VertexBallImage src f₁ w ∩ c '' section34VertexBallImage src f₁ w' =
        c '' (f₁ '' (src (.vertexBall w) ∩ src (.vertexBall w'))) := by
    intro w w' hw hw'
    have h2 := (c.injOn.mono (union_subset (hVc w hw) (hVc w' hw'))).image_inter
      (subset_union_left (s := section34VertexBallImage src f₁ w)) subset_union_right
    rw [hf₁.injOn.image_inter (hNV w) (hNV w')]
    exact h2.symm
  have hDfr : ∀ w w' : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 →
      Section34Incident w'.1 s.1 → w ≠ w' →
      c '' section34VertexBallImage src f₁ w ∩ c '' section34VertexBallImage src f₁ w' ⊆
        frontier (c '' section34VertexBallImage src f₁ w) := by
    intro w w' hw hw' hww
    rw [hinter2 w w' hw hw', ← (hBall w hw).2]
    exact image_mono (image_mono (src_vertexBall_inter_subset_srcBd hcut hww))
  obtain ⟨B, hBdef⟩ : ∃ B : I → Set (EuclideanSpace ℝ (Fin 3)),
      ∀ i, B i = c '' section34VertexBallImage src f₁ i.1 := ⟨_, fun _ => rfl⟩
  have hBb : ∀ i, IsPLBall 3 (B i) := fun i => by
    rw [hBdef]
    exact (hBall i.1 ((hIm _).mp i.2)).1
  have hD : ∀ i j : I, i ≠ j → (B i ∩ B j).Nonempty →
      IsPLBall 2 (B i ∩ B j) ∧ B i ∩ B j ⊆ frontier (B i) := by
    intro i j hij hne
    have hi := (hIm _).mp i.2
    have hj := (hIm _).mp j.2
    have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    simp only [hBdef] at hne ⊢
    refine ⟨?_, hDfr i.1 j.1 hi hj hij'⟩
    rw [hinter2 i.1 j.1 hi hj] at hne ⊢
    obtain ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩⟩ := hne
    obtain ⟨e, he⟩ := exists_splitDisk_src_eq_inter_vertexBall hcut hij' ⟨x, hx⟩
    rw [← he]
    have hDc : f₁ '' src (.splitDisk e) ⊆ c.source := by
      rw [he]
      exact (image_mono inter_subset_left).trans (hVc i.1 hi)
    obtain ⟨q, hq, -⟩ := (hDcell e).exists_isPLHomeomorphOn_image_chart hc hDc
    exact ⟨q, hq⟩
  have h3 : ∀ i j k : I, i ≠ j → k ≠ i → k ≠ j → Disjoint (B i ∩ B j) (B k) := by
    intro i j k hij hki hkj
    have hi := (hIm _).mp i.2
    have hj := (hIm _).mp j.2
    have hk := (hIm _).mp k.2
    simp only [hBdef]
    rw [hinter2 i.1 j.1 hi hj]
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨_, ⟨x, ⟨hxi, hxj⟩, rfl⟩, rfl⟩ ⟨_, ⟨x', hx'k, rfl⟩, hceq⟩
    have hx' : x' = x := hf₁.injOn (hNV k.1 hx'k) (hNV i.1 hxi)
      (c.injOn (hVc k.1 hk (mem_image_of_mem f₁ hx'k)) (hVc i.1 hi (mem_image_of_mem f₁ hxi))
        hceq)
    rw [hx'] at hx'k
    obtain ⟨e, he⟩ := exists_splitDisk_src_eq_inter_vertexBall hcut
      (fun h => hij (Subtype.ext h)) ⟨x, hxi, hxj⟩
    obtain ⟨w, w', -, hew, -⟩ := hends e
    have hxD : x ∈ src (.splitDisk e) := by
      rw [he]
      exact ⟨hxi, hxj⟩
    have hsub : ∀ u : Section34VertexIndex 𝒦 𝒦', x ∈ src (.vertexBall u) → u = w ∨ u = w' := by
      intro u hu
      have hue : ((u.1 : Finset Ea) : Set Ea) ⊆ (w.1 : Set Ea) ∪ (w'.1 : Set Ea) := by
        rw [← hew]
        exact Finset.coe_subset.mpr (hvertexEdge u e ⟨x, hu, hxD⟩)
      rcases eq_or_eq_of_card_eq_one_of_subset_union u.2.2.1 w.2.2.1 w'.2.2.1 hue with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    rcases hsub i.1 hxi with hi' | hi' <;> rcases hsub j.1 hxj with hj' | hj' <;>
      rcases hsub k.1 hx'k with hk' | hk'
    all_goals first
      | exact hij (Subtype.ext (hi'.trans hj'.symm))
      | exact hki (Subtype.ext (hk'.trans hi'.symm))
      | exact hkj (Subtype.ext (hk'.trans hj'.symm))
  have hTsc : section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source := by
    rw [hTs]
    exact iUnion_subset fun i => hVc i.1 ((hIm _).mp i.2)
  have hTscomp : IsCompact (section34FaceTorus (section34VertexBallImage src f₁) s) := by
    rw [hTs]
    exact isCompact_iUnion fun i => (hVcell i.1).isCompact
  have hcTs : c '' section34FaceTorus (section34VertexBallImage src f₁) s = ⋃ i, B i := by
    rw [hTs, image_iUnion]
    exact iUnion_congr fun i => (hBdef i).symm
  have hSurf : c '' frontier (section34FaceTorus (section34VertexBallImage src f₁) s) =
      frontier (⋃ i, B i) := by
    rw [c.image_frontier_of_isCompact hTscomp hTsc, hcTs]
  have hfrTsc : frontier (section34FaceTorus (section34VertexBallImage src f₁) s) ⊆ c.source :=
    hTscomp.isClosed.frontier_subset.trans hTsc
  have hTcclosed : IsClosed (⋃ i, B i) :=
    isClosed_iUnion_of_finite fun i => (hBb i).isPolyhedron.isClosed
  have hSc : IsCompact (frontier (⋃ i, B i)) :=
    (isCompact_iUnion fun i => (hBb i).isPolyhedron.isCompact).of_isClosed_subset
      isClosed_frontier hTcclosed.frontier_subset
  have hloc3 := fun x (hx : x ∈ frontier (⋃ i, B i)) =>
    exists_isOpen_inter_frontier_iUnion_eq_isPLSphere hBb hD h3 hx
  have hSplanar : ∀ x ∈ frontier (⋃ i, B i), ∃ W' : Set (EuclideanSpace ℝ (Fin 3)),
      IsOpen W' ∧ x ∈ W' ∧ ∃ U' : Set (EuclideanSpace ℝ (Fin 2)),
        IsOpen U' ∧ Nonempty (↥(W' ∩ frontier (⋃ i, B i)) ≃ₜ U') := by
    intro x hx
    obtain ⟨O, hO, hxO, T, hT, hOT⟩ := hloc3 x hx
    have hxT : x ∈ O ∩ T := by
      rw [← hOT]
      exact ⟨hxO, hx⟩
    exact exists_isOpen_inter_homeomorph_of_inter_eq hO hOT hxO
      (hT.exists_isOpen_inter_homeomorph_of_two hxT.2)
  have hSloc : IsLocallyPolyhedral (frontier (⋃ i, B i)) :=
    IsLocallyPolyhedral.of_forall_isOpen_inter_eq fun x hx => by
      obtain ⟨O, hO, hxO, T, hT, hOT⟩ := hloc3 x hx
      exact ⟨O, hO, hxO, T, hT.isPolyhedron, hOT⟩
  have hEends : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
      ∃ w w' : Section34VertexIndex 𝒦 𝒦', w ≠ w' ∧ Section34Incident w.1 s.1 ∧
        Section34Incident w'.1 s.1 ∧
        src (.splitDisk e) = src (.vertexBall w) ∩ src (.vertexBall w') := by
    intro e he
    obtain ⟨w, w', hww, hew, hDw⟩ := hends e
    have he' : (w.1 : Set Ea) ∪ (w'.1 : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea) := by
      rw [← hew]
      exact he
    exact ⟨w, w', hww, subset_union_left.trans he', subset_union_right.trans he', hDw⟩
  have hEc : ∀ e : Section34EdgeIndex 𝒦 𝒦', Section34Incident e.1 s.1 →
      f₁ '' src (.splitDisk e) ⊆ c.source := by
    intro e he
    obtain ⟨w, w', -, hw, -, hDw⟩ := hEends e he
    rw [hDw]
    exact (image_mono inter_subset_left).trans (hVc w hw)
  have hBdpoly : IsPolyhedron (stdSimplexBoundary 2) := by
    let _ : Finite (simplexBoundary (stdVertices 1) (stdVertices_affineIndependent 1)).faces :=
      (simplexBoundary_faces_finite _ _).to_subtype
    rw [← simplexBoundary_stdVertices_space 1]
    exact isPolyhedron_space _
  obtain ⟨J, hJdef⟩ : ∃ J : E' → Set (EuclideanSpace ℝ (Fin 3)),
      ∀ a, J a = c '' section34SplitDiskImage srcBd f₁ a.1 := ⟨_, fun _ => rfl⟩
  have hJ : ∀ a : E', IsPLSphere 1 (J a) ∧ J a ⊆ frontier (⋃ i, B i) := by
    intro a
    have ha := (hEm _).mp a.2
    obtain ⟨w, w', hww, hw, hw', hDw⟩ := hEends a.1 ha
    obtain ⟨q, hq, hqB⟩ := (hDcell a.1).exists_isPLHomeomorphOn_image_chart hc (hEc a.1 ha)
    have hJa : J a = q '' stdSimplexBoundary 2 := by
      rw [hJdef]
      exact hqB
    rw [hJa]
    refine ⟨⟨q, hq.restrict hBdpoly fun x hx => hx.1⟩, ?_⟩
    have hq' : IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3))
        (B ⟨w, (hIm _).mpr hw⟩ ∩ B ⟨w', (hIm _).mpr hw'⟩) := by
      rw [hBdef, hBdef, hinter2 w w' hw hw', ← hDw]
      exact hq
    have hDi : B ⟨w, (hIm _).mpr hw⟩ ∩ B ⟨w', (hIm _).mpr hw'⟩ ⊆
        frontier (B ⟨w, (hIm _).mpr hw⟩) := by
      rw [hBdef, hBdef]
      exact hDfr w w' hw hw' hww
    exact image_stdSimplexBoundary_subset_frontier_iUnion hBb h3
      (fun h => hww (congrArg Subtype.val h)) hq' hDi
  have hDdisj : ∀ e e' : Section34EdgeIndex 𝒦 𝒦', e ≠ e' →
      src (.splitDisk e) ∩ src (.splitDisk e') = ∅ := by
    intro e e' hee
    by_contra hne
    obtain ⟨x, hxe, hxe'⟩ := nonempty_iff_ne_empty.mpr hne
    have hsub : ∀ a b : Section34EdgeIndex 𝒦 𝒦', x ∈ src (.splitDisk a) →
        x ∈ src (.splitDisk b) → b.1 ⊆ a.1 := by
      intro a b ha hb
      obtain ⟨u, u', -, hbu, hDu⟩ := hends b
      have hb' : x ∈ src (.vertexBall u) ∩ src (.vertexBall u') := by
        rw [← hDu]
        exact hb
      rw [← Finset.coe_subset, hbu]
      exact union_subset (Finset.coe_subset.mpr (hvertexEdge u a ⟨x, hb'.1, ha⟩))
        (Finset.coe_subset.mpr (hvertexEdge u' a ⟨x, hb'.2, ha⟩))
    exact hee (Subtype.ext (Finset.Subset.antisymm (hsub e' e hxe' hxe) (hsub e e' hxe hxe')))
  have hJdisj : Pairwise fun a b : E' => Disjoint (J a) (J b) := by
    intro a b hab
    rw [hJdef, hJdef]
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ ⟨_, ⟨x', hx', rfl⟩, hceq⟩
    have hxa := (hcell (.splitDisk a.1)).boundary_subset hx
    have hxb := (hcell (.splitDisk b.1)).boundary_subset hx'
    have hx'x : x' = x := hf₁.injOn (hDN b.1 hxb) (hDN a.1 hxa)
      (c.injOn (hEc b.1 ((hEm _).mp b.2) (mem_image_of_mem f₁ hxb))
        (hEc a.1 ((hEm _).mp a.2) (mem_image_of_mem f₁ hxa)) hceq)
    rw [hx'x] at hxb
    exact absurd ((hDdisj a.1 b.1 fun h => hab (Subtype.ext h)).subset ⟨hxa, hxb⟩)
      (notMem_empty x)
  obtain ⟨G, hGfin, hGcard, hGsp⟩ :=
    exists_simplicialComplex_iUnion_isPLSphere_one (fun a => (hJ a).1) hJdisj
  have : Finite G.faces := hGfin.to_subtype
  have hGS : G.space ⊆ frontier (⋃ i, B i) := by
    rw [hGsp]
    exact iUnion_subset fun a => (hJ a).2
  have hJc : ∀ a : E', IsClosed (J a) := fun a => (hJ a).1.isPolyhedron.isClosed
  have hJloc : ∀ (a : E'), ∀ x ∈ J a, ∀ᶠ z in 𝓝 x,
      z ∈ G.space ↔ z ∈ c '' (section34SplitDiskImage srcBd f₁ a.1 ∩ c.source) := by
    intro a x hx
    have hO : IsOpen (⋃ b ∈ {b : E' | b ≠ a}, J b)ᶜ :=
      ((Set.toFinite _).isClosed_biUnion fun b _ => hJc b).isOpen_compl
    have hxO : x ∈ (⋃ b ∈ {b : E' | b ≠ a}, J b)ᶜ := by
      intro hx'
      obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hx'
      exact Set.disjoint_left.mp (hJdisj hb) hxb hx
    have hsrc : section34SplitDiskImage srcBd f₁ a.1 ∩ c.source =
        section34SplitDiskImage srcBd f₁ a.1 :=
      inter_eq_left.mpr ((image_mono (hcell (.splitDisk a.1)).boundary_subset).trans
        (hEc a.1 ((hEm _).mp a.2)))
    filter_upwards [hO.mem_nhds hxO] with z hz
    rw [hsrc, ← hJdef, hGsp]
    constructor
    · intro hzG
      obtain ⟨b, hzb⟩ := mem_iUnion.mp hzG
      by_cases hba : b = a
      · rw [hba] at hzb
        exact hzb
      · exact absurd (mem_biUnion (show b ∈ {b : E' | b ≠ a} from hba) hzb) hz
    · exact fun hza => mem_iUnion.mpr ⟨a, hza⟩
  obtain ⟨L, Cc, hLfin, hL, hCL, hCcard, hCB, hagree⟩ :=
    exists_isCombinatorialManifoldWithBoundary_two_curve_eventually_mem_iff hSplanar hSloc G
      hGcard hGS hSc Subset.rfl
  have : Finite L.faces := hLfin.to_subtype
  have hCc : C ⊆ c.source := hCW.trans hWc
  have hbodyW : h '' simplexBody 𝒦 s.1 ⊆ Wn := hbodyC.trans (interior_subset.trans hCW)
  have hhU : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hbodyU : simplexBody 𝒦 s.1 ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    exact 𝒦.bijOn.mapsTo (𝒦.complex.convexHull_subset_space s.2.1 hx)
  have hbodyc : IsCompact (simplexBody 𝒦 s.1) :=
    (s.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).image_of_continuousOn
      (𝒦.continuousOn.mono (𝒦.complex.convexHull_subset_space s.2.1))
  have hAc : IsCompact (c '' (h '' simplexBody 𝒦 s.1)) :=
    (hbodyc.image_of_continuousOn (hhU.mono hbodyU)).image_of_continuousOn
      (c.continuousOn.mono (hbodyW.trans hWc))
  have hAP : c '' (h '' simplexBody 𝒦 s.1) ⊆ interior (c '' C) :=
    (image_mono hbodyC).trans (interior_maximal (image_mono interior_subset)
      (c.isOpen_image_of_subset_source isOpen_interior (interior_subset.trans hCc)))
  have hUo : IsOpen (c '' Wn) := c.isOpen_image_of_subset_source hWo hWc
  obtain ⟨P', hP', hAP', hP'U, hcross, hcurve, hfinC, M, N, hMfin, hNM, hMsp, hNsp, hMN⟩ :=
    exists_isPLBall_transverse_of_isPLBall (hC.isPLBall_image_chart hc hCc).1 hAc hAP hUo
      (image_mono hCW) L Cc hL hCL hCcard (by convert hCB)
  have : Finite M.faces := hMfin.to_subtype
  have hWt' : c '' Wn ⊆ c.target := by
    rintro _ ⟨y, hy, rfl⟩
    exact c.map_source (hWc hy)
  have hP't : P' ⊆ c.target := hP'U.trans hWt'
  have hP'c : IsClosed P' := hP'.isPolyhedron.isClosed
  have hfrt : frontier P' ⊆ c.target := hP'c.frontier_subset.trans hP't
  obtain ⟨r, hr⟩ := id hP'
  have hfr : r '' stdSimplexBoundary 3 = frontier P' :=
    IsPLHomeomorphOn.image_stdSimplexBoundary (n := 2) hr
  have hFcell : IsPLCellOn 3 (c.symm '' P') (c.symm '' frontier P') :=
    ⟨P', r, c.symm, hr, isPLHomeomorphInto_symm_of_mem_maximalAtlas hc hP'.isPolyhedron hP't,
      rfl, by rw [hfr]⟩
  have hFW : c.symm '' P' ⊆ Wn := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hP'U hx
    rw [c.left_inv (hWc hy)]
    exact hy
  have hFbW : c.symm '' frontier P' ⊆ Wn := (image_mono hP'c.frontier_subset).trans hFW
  have hFbsrc : c.symm '' frontier P' ⊆ c.source := hFbW.trans hWc
  have hcFb : c '' (c.symm '' frontier P') = frontier P' := c.image_symm_image_of_subset_target hfrt
  have hFbfr : ∀ y ∈ c.symm '' frontier P', c y ∈ frontier P' := fun y hy => by
    rw [← hcFb]
    exact mem_image_of_mem c hy
  have hrimbody : simplexRim 𝒦 s.1 ⊆ simplexBody 𝒦 s.1 := by
    intro x hx
    obtain ⟨τ, hτ, hxτ⟩ := mem_iUnion₂.mp hx
    exact image_mono (convexHull_mono (Finset.coe_subset.mpr hτ.1)) hxτ
  have hbodyF : h '' simplexBody 𝒦 s.1 ⊆ interior (c.symm '' P') := by
    intro y hy
    refine interior_maximal (image_mono interior_subset)
      (c.isOpen_image_symm_of_subset_target isOpen_interior (interior_subset.trans hP't)) ?_
    exact ⟨c y, hAP' (mem_image_of_mem c hy), c.left_inv (hWc (hbodyW hy))⟩
  have hrimF : h '' simplexRim 𝒦 s.1 ⊆ interior (c.symm '' P') :=
    (image_mono hrimbody).trans hbodyF
  have hUW : (⋃ w, section34VertexBallImage src f₁ w) ∩ Wn =
      section34FaceTorus (section34VertexBallImage src f₁) s ∩ Wn := by
    apply Subset.antisymm
    · rintro y ⟨hy, hyW⟩
      obtain ⟨w, hyw⟩ := mem_iUnion.mp hy
      by_cases hw : Section34Incident w.1 s.1
      · rw [hTs]
        exact ⟨mem_iUnion.mpr ⟨⟨w, (hIm w).mpr hw⟩, hyw⟩, hyW⟩
      · have hmem : y ∈ Wn ∩ section34VertexBallImage src f₁ w := ⟨hyW, hyw⟩
        rw [hWV w hw] at hmem
        exact absurd hmem (notMem_empty y)
    · rintro y ⟨hy, hyW⟩
      rw [hTs] at hy
      obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
      exact ⟨mem_iUnion.mpr ⟨i.1, hyi⟩, hyW⟩
  have hR0 : frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ Wn =
      frontier (section34FaceTorus (section34VertexBallImage src f₁) s) ∩ Wn := by
    rw [← frontier_inter_open_inter hWo, hUW, frontier_inter_open_inter hWo]
  have hR1 : ∀ x ∈ c '' Wn, ∀ᶠ z in 𝓝 x,
      z ∈ c '' (frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ c.source) ↔
        z ∈ frontier (⋃ i, B i) := by
    have hsets : Wn ∩ (frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ c.source) =
        Wn ∩ frontier (section34FaceTorus (section34VertexBallImage src f₁) s) := by
      rw [inter_comm Wn (frontier _), ← hR0]
      ext y
      exact ⟨fun ⟨hyW, hyX, _⟩ => ⟨hyX, hyW⟩, fun ⟨hyX, hyW⟩ => ⟨hyW, hyX, hWc hyW⟩⟩
    have heq : c '' Wn ∩ c '' (frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ c.source) =
        c '' Wn ∩ frontier (⋃ i, B i) := by
      rw [← c.injOn.image_inter hWc inter_subset_right, hsets,
        c.injOn.image_inter hWc hfrTsc, hSurf]
    intro x hx
    filter_upwards [hUo.mem_nhds hx] with z hz
    have hz' := Set.ext_iff.mp heq z
    exact ⟨fun hzA => (hz'.mp ⟨hz, hzA⟩).2, fun hzB => (hz'.mpr ⟨hz, hzB⟩).2⟩
  have hFbX : ∀ y ∈ c.symm '' frontier P', y ∈ frontier (⋃ w, section34VertexBallImage src f₁ w) →
      c y ∈ frontier (⋃ i, B i) := by
    intro y hyFb hyX
    have hy : y ∈ frontier (section34FaceTorus (section34VertexBallImage src f₁) s) ∩ Wn := by
      rw [← hR0]
      exact ⟨hyX, hFbW hyFb⟩
    rw [← hSurf]
    exact mem_image_of_mem c hy.1
  have hEinc : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (y : M₂), y ∈ Wn →
      y ∈ section34SplitDiskImage srcBd f₁ e → Section34Incident e.1 s.1 := by
    intro e y hyW hye
    obtain ⟨w, w', -, hew, hDw⟩ := hends e
    obtain ⟨x, hx, rfl⟩ := hye
    have hxD := (hcell (.splitDisk e)).boundary_subset hx
    rw [hDw] at hxD
    have hinc1 : ∀ u : Section34VertexIndex 𝒦 𝒦', x ∈ src (.vertexBall u) →
        Section34Incident u.1 s.1 := by
      intro u hu
      by_contra hn
      have hmem : f₁ x ∈ Wn ∩ section34VertexBallImage src f₁ u := ⟨hyW, mem_image_of_mem f₁ hu⟩
      rw [hWV u hn] at hmem
      exact hmem
    change (e.1 : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
    rw [hew]
    exact union_subset (hinc1 w hxD.1) (hinc1 w' hxD.2)
  have hEdgeC : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (y : M₂), y ∈ c.symm '' frontier P' →
      y ∈ section34SplitDiskImage srcBd f₁ e → ∃ a : E', a.1 = e ∧ c y ∈ J a ∧
        c y ∈ frontier (⋃ i, B i) ∧ c y ∈ Cc.space := by
    intro e y hyFb hye
    have he := hEinc e y (hFbW hyFb) hye
    have hxJ : c y ∈ J ⟨e, (hEm _).mpr he⟩ := by
      rw [hJdef]
      exact mem_image_of_mem c hye
    have hxG : c y ∈ G.space := by
      rw [hGsp]
      exact mem_iUnion.mpr ⟨_, hxJ⟩
    exact ⟨⟨e, (hEm _).mpr he⟩, rfl, hxJ, hGS hxG,
      ((hagree (c y) (hGS hxG)).self_of_nhds).2.mpr hxG⟩
  have hV1 : IsOpen {z | ∀ᶠ y in 𝓝 z, (y ∈ L.space ↔ y ∈ frontier (⋃ i, B i))} :=
    isOpen_setOfPred_eventually_nhds
  have hK1 : ∀ σ ∈ M.faces, (openSimplex σ ∩ frontier (⋃ i, B i)).Nonempty →
      convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 3))) ⊆ frontier (⋃ i, B i) := by
    rintro σ hσ ⟨z, hzσ, hzS⟩
    have hzL : z ∈ L.space := ((hagree z hzS).self_of_nhds).1.mpr hzS
    by_cases hσN : σ ∈ N.faces
    · have hσL : convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 3))) ⊆ L.space :=
        (N.convexHull_subset_space hσN).trans (by rw [hNsp]; exact inter_subset_right)
      have hcover : convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 3))) ⊆
          {z | ∀ᶠ y in 𝓝 z, (y ∈ L.space ↔ y ∈ frontier (⋃ i, B i))} ∪
            (frontier (⋃ i, B i))ᶜ := by
        intro y _
        by_cases hyS : y ∈ frontier (⋃ i, B i)
        · exact Or.inl ((hagree y hyS).mono fun _ h => h.1)
        · exact Or.inr hyS
      have hdis : convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 3))) ∩
          ({z | ∀ᶠ y in 𝓝 z, (y ∈ L.space ↔ y ∈ frontier (⋃ i, B i))} ∩
            (frontier (⋃ i, B i))ᶜ) = ∅ := by
        refine eq_empty_iff_forall_notMem.mpr fun y hy => hy.2.2 ?_
        exact (Filter.Eventually.self_of_nhds hy.2.1).mp (hσL hy.1)
      rcases isPreconnected_iff_subset_of_disjoint.mp
        (convex_convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 3)))).isPreconnected _ _ hV1
        isClosed_frontier.isOpen_compl hcover hdis with hsub | hsub
      · exact fun y hy => (Filter.Eventually.self_of_nhds (hsub hy)).mp (hσL hy)
      · exact absurd hzS (hsub (openSimplex_subset_convexHull σ hzσ))
    · exact absurd hzL (Set.disjoint_left.mp (hMN σ hσ hσN) hzσ)
  have hK2 : ∀ σ ∈ M.faces, (openSimplex σ ∩ ⋃ i, B i).Nonempty →
      convexHull ℝ (σ : Set (EuclideanSpace ℝ (Fin 3))) ⊆ ⋃ i, B i := by
    intro σ hσ hne
    by_cases hS : (openSimplex σ ∩ frontier (⋃ i, B i)).Nonempty
    · exact (hK1 σ hσ hS).trans hTcclosed.frontier_subset
    · have hdis : Disjoint (openSimplex σ) (frontier (⋃ i, B i)) :=
        Set.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hS)
      have hsub := IsPreconnected.subset_of_disjoint_frontier
        (convex_openSimplex σ).isPreconnected hne hdis
      exact (convexHull_subset_closure_openSimplex (M.nonempty_of_mem_faces hσ)).trans
        (closure_minimal hsub hTcclosed)
  have : Finite (restrict M (⋃ i, B i)).faces := (restrict_faces_finite M _).to_subtype
  have : Finite (restrict M (frontier (⋃ i, B i))).faces :=
    (restrict_faces_finite M _).to_subtype
  have hB0 : (restrict M (frontier (⋃ i, B i))).space = frontier P' ∩ frontier (⋃ i, B i) := by
    rw [restrict_space_eq_inter_of_openSimplex M hK1, hMsp]
  have hBsp : (restrict M (frontier (⋃ i, B i))).space =
      c '' (c.symm '' frontier P' ∩
        frontier (section34FaceTorus (section34VertexBallImage src f₁) s)) := by
    rw [hB0, c.injOn.image_inter hFbsrc hfrTsc, hcFb, hSurf]
  have hAsp : (restrict M (⋃ i, B i)).space =
      c '' (c.symm '' frontier P' ∩ section34FaceTorus (section34VertexBallImage src f₁) s) := by
    rw [restrict_space_eq_inter_of_openSimplex M hK2, hMsp, c.injOn.image_inter hFbsrc hTsc,
      hcFb, hcTs]
  have hBA : (restrict M (frontier (⋃ i, B i))).faces ⊆ (restrict M (⋃ i, B i)).faces :=
    fun σ hσ => ⟨hσ.1, hσ.2.trans hTcclosed.frontier_subset⟩
  refine ⟨c.symm '' P', c.symm '' frontier P', hFcell, hrimF, hFW, ?_, ?_, ?_, ?_, ?_⟩
  · rintro y ⟨hyFb, hyX⟩
    have hxS := hFbX y hyFb hyX
    have hxL : c y ∈ L.space := ((hagree (c y) hxS).self_of_nhds).1.mpr hxS
    refine ⟨c, hc, hFbsrc hyFb, (hcross (c y) ⟨hFbfr y hyFb, hxL⟩).congr ?_ ?_⟩
    · rw [inter_eq_left.mpr hFbsrc, hcFb]
      exact Filter.Eventually.of_forall fun _ => Iff.rfl
    · filter_upwards [hagree (c y) hxS, hR1 (c y) (mem_image_of_mem c (hFbW hyFb))]
        with z hz1 hz2
      exact hz1.1.trans hz2.symm
  · rintro e y ⟨hyFb, hye⟩
    obtain ⟨a, rfl, hxJ, hxS, hxC⟩ := hEdgeC e y hyFb hye
    have hFbXsrc : c '' (c.symm '' frontier P' ∩ frontier (⋃ w, section34VertexBallImage src f₁ w)
        ∩ c.source) =
        frontier P' ∩ c '' (frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ c.source) := by
      rw [inter_assoc, c.injOn.image_inter hFbsrc inter_subset_right, hcFb]
    refine ⟨c, hc, hFbsrc hyFb, (hcurve (c y) ⟨hFbfr y hyFb, hxC⟩).congr ?_ ?_ ?_⟩
    · filter_upwards [hagree (c y) hxS, hR1 (c y) (mem_image_of_mem c (hFbW hyFb))]
        with z hz1 hz2
      exact hz1.1.trans hz2.symm
    · filter_upwards [hagree (c y) hxS, hR1 (c y) (mem_image_of_mem c (hFbW hyFb))]
        with z hz1 hz2
      rw [hFbXsrc, mem_inter_iff, mem_inter_iff]
      exact and_congr Iff.rfl (hz1.1.trans hz2.symm)
    · filter_upwards [hagree (c y) hxS, hJloc a (c y) hxJ] with z hz1 hz2
      exact hz1.2.trans hz2
  · have hFC' : c.symm '' P' ∩ C' ⊆
        interior (section34FaceTorus (section34VertexBallImage src f₁) s) := by
      rintro y ⟨hyF, hyC'⟩
      by_contra hyi
      exact Set.disjoint_left.mp hWC' (hFW hyF) ⟨hyC', hyi⟩
    have hstep1 := hFcell.carriesFirstHomologyOnto_inter_interior hC'c hC'1 hRC' hrimF hFC'
      (carriesFirstHomologyOnto_image_simplexRim hh hcut hgraph s)
    have hFbc : IsCompact (c.symm '' frontier P') :=
      (hP'.isPolyhedron.isCompact.of_isClosed_subset isClosed_frontier
        hP'c.frontier_subset).image_of_continuousOn (c.continuousOn_symm.mono hfrt)
    exact hstep1.inter_frontier_of_chart hFbc.isClosed hTscomp.isClosed
      hFcell.subsingleton_integralSingularHomology_one_boundary hFbsrc
      (restrict M (⋃ i, B i)) (restrict M (frontier (⋃ i, B i))) hBA hAsp hBsp
  · refine (hfinC.image c.symm).subset ?_
    rintro y ⟨hyFb, hyE⟩
    obtain ⟨e, hye⟩ := mem_iUnion.mp hyE
    obtain ⟨-, -, -, -, hxC⟩ := hEdgeC e y hyFb hye
    exact ⟨c y, ⟨hFbfr y hyFb, hxC⟩, c.left_inv (hFbsrc hyFb)⟩
  · have hBspU : (restrict M (frontier (⋃ i, B i))).space =
        ⋃ σ : (restrict M (frontier (⋃ i, B i))).faces,
          convexHull ℝ (σ.1 : Set (EuclideanSpace ℝ (Fin 3))) := by
      ext x
      rw [Geometry.SimplicialComplex.mem_space_iff, mem_iUnion]
      exact ⟨fun ⟨σ, hσ, hx⟩ => ⟨⟨σ, hσ⟩, hx⟩, fun ⟨σ, hx⟩ => ⟨σ.1, σ.2, hx⟩⟩
    have htrace : c.symm '' frontier P' ∩ frontier (⋃ w, section34VertexBallImage src f₁ w) =
        ⋃ σ : (restrict M (frontier (⋃ i, B i))).faces,
          c.symm '' convexHull ℝ (σ.1 : Set (EuclideanSpace ℝ (Fin 3))) := by
      have h1 : c.symm '' frontier P' ∩ frontier (⋃ w, section34VertexBallImage src f₁ w) =
          c.symm '' frontier P' ∩
            frontier (section34FaceTorus (section34VertexBallImage src f₁) s) := by
        ext y
        constructor
        · rintro ⟨hyFb, hyX⟩
          have hy : y ∈ frontier (section34FaceTorus (section34VertexBallImage src f₁) s) ∩ Wn :=
            by rw [← hR0]; exact ⟨hyX, hFbW hyFb⟩
          exact ⟨hyFb, hy.1⟩
        · rintro ⟨hyFb, hyT⟩
          have hy : y ∈ frontier (⋃ w, section34VertexBallImage src f₁ w) ∩ Wn := by
            rw [hR0]
            exact ⟨hyT, hFbW hyFb⟩
          exact ⟨hyFb, hy.1⟩
      rw [h1, ← image_iUnion, ← hBspU, hBsp]
      exact (c.symm_image_image_of_subset_source (inter_subset_left.trans hFbsrc)).symm
    refine finite_image_connectedComponentIn_of_eq_iUnion (fun σ => ?_) htrace
    have hσt : convexHull ℝ (σ.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆ c.target := by
      refine ((restrict M _).convexHull_subset_space σ.2).trans ?_
      rw [hB0]
      exact inter_subset_left.trans hfrt
    exact (convex_convexHull ℝ _).isPreconnected.image c.symm (c.continuousOn_symm.mono hσt)

end FaceBall

section Assembly

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

theorem exists_section34FaceBalls (hU : IsOpen U)
    (hh : Topology.IsEmbedding (U.domRestrict h))
    (hcut : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hctrl : Section34CarrierControl U 𝒦 h η H)
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁) :
    ∃ fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂,
      Section34FaceBallInvariants 𝒦 𝒦' h H (section34VertexBallImage src f₁)
        (section34SplitDiskImage srcBd f₁) fbl fblBd := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcof⟩ :=
    id hcut
  choose C' hC'c hC'1 hRC' hC'dis using exists_section34FaceTorusAuxiliary hh hcut hgraph
  obtain ⟨Wn, -, -, hWo, -, -, hWH, hWV, hWW, hWS, hWbad, hcell⟩ :=
    exists_section34FaceBallNeighborhoods hU hh hcut hctrl hgraph
      (fun s => C' s \ interior (section34FaceTorus (section34VertexBallImage src f₁) s))
      (fun s => (hC'c s).isClosed.sdiff isOpen_interior) hC'dis
  choose C Cb hC hbodyC hCW using hcell
  choose fbl fblBd hcellF hrimF hFW h5 h6 h7 h8 h9 using fun s =>
    (hcof s).elim fun t hst => exists_section34FaceBall_of_neighborhood hh hcut hctrl hgraph s
      hst (hWo s) (hWH s t hst) (hWV s) (hC s) (hbodyC s) (hCW s) (hC'c s) (hC'1 s) (hRC' s)
      (hWbad s)
  have hV : ∀ (s : Section34SimplexIndex 𝒦 3) (w : Section34VertexIndex 𝒦 𝒦'),
      ¬ Section34Incident w.1 s.1 → fbl s ∩ section34VertexBallImage src f₁ w = ∅ :=
    fun s w hw => subset_eq_empty (inter_subset_inter_left _ (hFW s)) (hWV s w hw)
  refine ⟨fbl, fblBd, hcellF, hrimF, hV, fun s s' hss' =>
    (inter_subset_inter (hFW s) (hFW s')).trans (hWW s s' hss'), h5, h6, h7, h8, h9, ?_⟩
  exact section34Exterior_of_subset hh hcut hctrl hgraph (fun s => (hcellF s).isCompact.isClosed)
    (fun s t hst => (hFW s).trans (hWH s t hst)) hV (fun s => (hFW s).trans (hWS s))

end Assembly

end DifferentialGeometry.Topology.PiecewiseLinear
