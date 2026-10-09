/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BallWindingObstruction
import DifferentialGeometry.Topology.PiecewiseLinear.LabelledCellAssemblyWitness
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TraceArcs
import DifferentialGeometry.Topology.PiecewiseLinear.SphereInnermostDisk

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Diagram

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}
  {tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {fbl fblBd tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂}
  {tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂}
  {tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂}
  {tgtR tgtRBd : Section34SimplexIndex 𝒦 4 → Set M₂}
  {tgtX tgtXBd : Section34PatchIndex 𝒦 𝒦' → Set M₂}
  {tgtI tgtIBd : Section34EdgeArcIndex 𝒦 𝒦' → Set M₂}

theorem exists_section34FaceDisks
    (hdata : Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd
      fbl fblBd) :
    ∃ (tgtD tgtDBd : Section34SimplexIndex 𝒦 3 → Set M₂)
      (tgtA tgtABd : Section34ArcIndex 𝒦 𝒦' → Set M₂)
      (tgtP : Section34MarkIndex 𝒦 𝒦' → Set M₂),
      Section34FaceDiskFamily 𝒦 𝒦' tgtV tgtE tgtEBd fblBd tgtD tgtDBd tgtA tgtABd tgtP := by
  classical
  obtain ⟨hcut, hctrl, hgraph, hext, htrace, htgtV, htgtE, -, hEcell, -, -, -, hfcell, hfavoid,
    hfover, -, -⟩ := hdata
  obtain ⟨-, hsub, hmap, -⟩ := id hcut
  obtain ⟨-, -, hf₁, -⟩ := id hgraph
  have hinj : InjOn f₁ (section34CutNeighborhood src) := hf₁.injOn
  have hEc' : ∀ e, IsPLCellOn 2 (tgtE e) (section34SplitDiskImage srcBd f₁ e) := fun e => by
    rw [htgtE e]
    exact hcut.isPLCellOn_splitDiskImage hf₁ e
  have hV : tgtV = section34VertexBallImage src f₁ := funext htgtV
  have hE : tgtE = section34SplitDiskImage src f₁ := funext htgtE
  have hEBd : tgtEBd = section34SplitDiskImage srcBd f₁ :=
    funext fun e => (hEcell e).boundary_eq (hEc' e)
  subst hV hE hEBd
  obtain ⟨r, J, hr, hJs, hJd, hJU, hJT, hJe⟩ := htrace
  obtain ⟨hext1, -, -⟩ := hext
  obtain ⟨-, -, -, -, -, hchart⟩ := hctrl
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcof⟩ :=
    id hcut
  have hchartS : ∀ s : Section34SimplexIndex 𝒦 3, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂,
      fbl s ⊆ c.source ∧ section34FaceTorus (section34VertexBallImage src f₁) s ⊆ c.source := by
    intro s
    obtain ⟨t, hst⟩ := hcof s
    obtain ⟨c, hc, hHc⟩ := hchart t.1 t.2.1
    refine ⟨c, hc, fun x hx => hHc (interior_subset (hext1 t ?_)),
      fun x hx => hHc (interior_subset (hext1 t ?_))⟩
    · exact Or.inr (mem_iUnion₂.mpr ⟨s, hst, hx⟩)
    · obtain ⟨w, hw, hxw⟩ := mem_section34FaceTorus_iff.mp hx
      have hwt : Section34Incident w.1 t.1 :=
        Subset.trans hw (convexHull_min hst (convex_convexHull ℝ _))
      exact Or.inl (mem_iUnion₂.mpr ⟨⟨(t, w), hwt⟩, rfl, hxw⟩)
  choose c hc hfc hTc using hchartS
  have hfsub : ∀ s, fblBd s ⊆ fbl s := fun s => (hfcell s).boundary_subset
  have hVcell := hcut.isPLCellOn_vertexBallImage hf₁
  have hVcl : ∀ w, IsClosed (section34VertexBallImage src f₁ w) :=
    fun w => (hVcell w).isCompact.isClosed
  have hEbdE : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      section34SplitDiskImage srcBd f₁ e ⊆ section34SplitDiskImage src f₁ e :=
    fun e => (hcut.isPLCellOn_splitDiskImage hf₁ e).boundary_subset
  have hJS : ∀ s, ∀ i < r s,
      J s i ⊆ fblBd s ∩ frontier (⋃ w, section34VertexBallImage src f₁ w) := by
    intro s i hi
    rw [hJU s]
    exact subset_iUnion₂ (s := fun i (_ : i < r s) => J s i) i hi
  have hJT' : ∀ s, ∀ i < r s,
      J s i ⊆ frontier (section34FaceTorus (section34VertexBallImage src f₁) s) := by
    intro s i hi
    have hsubJ := subset_iUnion₂ (s := fun i (_ : i < r s) => J s i) i hi
    rw [← hJT s] at hsubJ
    exact hsubJ.trans inter_subset_right
  have hJTs : ∀ s, ∀ i < r s, J s i ⊆ section34FaceTorus (section34VertexBallImage src f₁) s :=
    fun s i hi => (hJT' s i hi).trans (isClosed_section34FaceTorus hsub hVcl s).frontier_subset
  have hJc : ∀ s, ∀ i < r s, J s i ⊆ (c s).source := fun s i hi => (hJTs s i hi).trans (hTc s)
  have hJf : ∀ s, ∀ i < r s, J s i ⊆ fbl s :=
    fun s i hi => ((hJS s i hi).trans inter_subset_left).trans (hfsub s)
  have hball : ∀ s, IsPLBall 3 ((c s) '' fbl s) ∧ (c s) '' fblBd s = frontier ((c s) '' fbl s) :=
    fun s => (hfcell s).isPLBall_image_chart (hc s) (hfc s)
  have hsi : ∀ s {X : Set M₂}, X ⊆ (c s).source → (c s).symm '' ((c s) '' X) = X :=
    fun s _ hX => (c s).symm_image_image_of_subset_source hX
  have hft : ∀ s, (c s) '' fbl s ⊆ (c s).target := by
    rintro s _ ⟨x, hx, rfl⟩
    exact (c s).map_source (hfc s hx)
  have hJsph : ∀ s, ∀ i < r s, IsPLSphere 1 ((c s) '' J s i) := by
    intro s i hi
    refine (hJs s i hi).isPLSphere_image_of_mem_maximalAtlas (hc s) (hball s).1.isPolyhedron
      (hft s) fun x hx => ?_
    exact ⟨c s x, mem_image_of_mem _ (hJf s i hi hx), (c s).left_inv (hfc s (hJf s i hi hx))⟩
  have harcs : ∀ s, ∀ i < r s, ∀ w : Section34VertexIndex 𝒦 𝒦', Section34Incident w.1 s.1 →
      IsPLCellOn 1 (J s i ∩ section34VertexBallImage src f₁ w)
          (J s i ∩ section34VertexBallImage src f₁ w ∩ ⋃ e, section34SplitDiskImage src f₁ e) ∧
        IsPreconnected (J s i ∩ ⋃ (u : Section34VertexIndex 𝒦 𝒦')
          (_ : Section34Incident u.1 s.1 ∧ u ≠ w), section34VertexBallImage src f₁ u) :=
    fun s i hi w hw => hcut.isPLCellOn_inter_vertexBallImage_of_chart hf₁ (hc s) (hTc s)
      (hJsph s i hi) (hJf s i hi) (fun w hw => hfavoid s w hw) (hJT' s i hi) (hJe s i hi) hw
  have hmemV : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (u : Section34VertexIndex 𝒦 𝒦') (x : M₂),
      x ∈ section34SplitDiskImage src f₁ e → u.1 ⊆ e.1 → x ∈ section34VertexBallImage src f₁ u := by
    intro e u x hx hu
    obtain ⟨a, b, -, hab, hEeq⟩ := hcut.splitDiskImage_eq_inter hinj e
    rw [hEeq] at hx
    rcases eq_or_eq_of_section34VertexIndex_subset e hab hu with h | h
    · rw [h]
      exact hx.1
    · rw [h]
      exact hx.2
  have hdisk : ∀ s : Section34SimplexIndex 𝒦 3, ∃ i < r s, ∃ D : Set M₂, IsPLCellOn 2 D (J s i) ∧
      D ⊆ fblBd s ∧ D ∩ ⋃ w, section34VertexBallImage src f₁ w = J s i := by
    intro s
    have _ : Nonempty (Fin (r s)) := ⟨⟨0, hr s⟩⟩
    have hS' : IsPLSphere 2 ((c s) '' fblBd s) := by
      rw [(hball s).2]
      exact (hball s).1.isPLSphere_frontier
    obtain ⟨k, D', q, hq, hD'S, hqJ, hD'k⟩ := hS'.exists_innermost_disk
      (J := fun k : Fin (r s) => (c s) '' J s k) (fun k => hJsph s k k.2)
      (fun k => image_mono ((hJS s k k.2).trans inter_subset_left)) (fun k k' hkk' => by
        refine Set.disjoint_left.mpr ?_
        rintro _ ⟨x, hx, rfl⟩ ⟨x', hx', hxx'⟩
        have hx'x : x' = x := (c s).injOn (hJc s k' k'.2 hx') (hJc s k k.2 hx) hxx'
        exact Set.disjoint_left.mp (hJd s k k.2 k' k'.2 fun h => hkk' (Fin.ext h)) hx
          (hx'x ▸ hx'))
    have hqJ' : q '' stdSimplexBoundary 2 = (c s) '' J s k := hqJ
    have hfbt : (c s) '' fblBd s ⊆ (c s).target := (image_mono (hfsub s)).trans (hft s)
    have hD't : D' ⊆ (c s).target := hD'S.trans hfbt
    have hJ'D' : (c s) '' J s k ⊆ D' := by
      rw [← hqJ', ← hq.image_eq]
      exact image_mono fun x hx => hx.1
    have hDcell : IsPLCellOn 2 ((c s).symm '' D') (J s k) := by
      have hcell := (isPLCellOn_id_of_isPLBall hq).image_chart_symm (hc s) hD't
      rwa [hqJ', hsi s (hJc s k k.2)] at hcell
    have hDS : (c s).symm '' D' ⊆ fblBd s :=
      (image_mono hD'S).trans (hsi s ((hfsub s).trans (hfc s))).subset
    have hJD : J s k ⊆ (c s).symm '' D' := by
      rw [← hsi s (hJc s k k.2)]
      exact image_mono hJ'D'
    have hinjD' : InjOn (c s).symm D' :=
      (c s).symm.injOn.mono (by rw [OpenPartialHomeomorph.symm_source]; exact hD't)
    have hpre : IsPreconnected ((c s).symm '' D' \ J s k) := by
      have h1 : q '' openSimplex (stdVertices 1) = D' \ q '' stdSimplexBoundary 2 :=
        IsPLHomeomorphOn.image_openSimplex_stdVertices hq
      have h2 : IsPreconnected (D' \ (c s) '' J s k) := by
        rw [← hqJ', ← h1]
        exact (convex_openSimplex _).isPreconnected.image q
          (hq.isPiecewiseAffineOn.continuousOn.mono openSimplex_stdVertices_subset_stdSimplex)
      have h3 := h2.image (c s).symm ((c s).continuousOn_symm.mono (sdiff_subset.trans hD't))
      rwa [hinjD'.image_sdiff_subset hJ'D', hsi s (hJc s k k.2)] at h3
    have hfr : Disjoint ((c s).symm '' D' \ J s k)
        (frontier (⋃ w, section34VertexBallImage src f₁ w)) := by
      refine Set.disjoint_left.mpr fun y hy hyU => ?_
      have hyJ : y ∈ ⋃ i < r s, J s i := by
        rw [← hJU s]
        exact ⟨hDS hy.1, hyU⟩
      obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hyJ
      by_cases hik : i = k.val
      · subst hik
        exact hy.2 hyi
      · obtain ⟨z, hz, hzy⟩ := hy.1
        have hz' : z ∈ (c s) '' J s i := ⟨y, hyi, by rw [← hzy]; exact (c s).right_inv (hD't hz)⟩
        exact Set.disjoint_left.mp (hD'k ⟨i, hi⟩ fun h => hik (congrArg Fin.val h)) hz hz'
    have hJU' : J s k ⊆ ⋃ w, section34VertexBallImage src f₁ w := fun x hx => by
      obtain ⟨w, -, hxw⟩ := mem_section34FaceTorus_iff.mp (hJTs s k k.2 hx)
      exact mem_iUnion.mpr ⟨w, hxw⟩
    refine ⟨k, k.2, (c s).symm '' D', hDcell, hDS,
      Subset.antisymm (fun y hy => ?_) (subset_inter hJD hJU')⟩
    by_contra hyk
    have hDU : (c s).symm '' D' \ J s k ⊆ ⋃ w, section34VertexBallImage src f₁ w :=
      IsPreconnected.subset_of_disjoint_frontier hpre ⟨y, ⟨hy.1, hyk⟩, hy.2⟩ hfr
    have hDinc : ∀ z ∈ (c s).symm '' D', ∃ w : Section34VertexIndex 𝒦 𝒦',
        Section34Incident w.1 s.1 ∧ z ∈ section34VertexBallImage src f₁ w := by
      intro z hz
      have hzU : z ∈ ⋃ w, section34VertexBallImage src f₁ w := by
        by_cases hzk : z ∈ J s k
        · exact hJU' hzk
        · exact hDU ⟨hz, hzk⟩
      obtain ⟨w, hzw⟩ := mem_iUnion.mp hzU
      refine ⟨w, ?_, hzw⟩
      by_contra hn
      have hmem : z ∈ fbl s ∩ section34VertexBallImage src f₁ w := ⟨hfsub s (hDS hz), hzw⟩
      rw [hfavoid s w hn] at hmem
      exact hmem
    obtain ⟨x₀, hx₀⟩ : (J s k).Nonempty := by
      obtain ⟨_, x₀, hx₀, -⟩ := (hJsph s k k.2).nonempty
      exact ⟨x₀, hx₀⟩
    obtain ⟨a, ha, -⟩ := mem_section34FaceTorus_iff.mp (hJTs s k k.2 hx₀)
    obtain ⟨e₀, e₁, he, hi₀, hi₁, ha₀, ha₁, huniq⟩ :=
      exists_section34EdgeIndex_pair_of_incident hsub hmap s a ha
    obtain ⟨hcellA, hpreB⟩ := harcs s k k.2 a ha
    obtain ⟨p₀, hp₀⟩ := hJe s k k.2 e₀ hi₀
    obtain ⟨p₁, hp₁⟩ := hJe s k k.2 e₁ hi₁
    have hp₀J : p₀ ∈ J s k ∩ section34SplitDiskImage srcBd f₁ e₀ := by
      rw [hp₀]
      exact mem_singleton _
    have hp₁J : p₁ ∈ J s k ∩ section34SplitDiskImage srcBd f₁ e₁ := by
      rw [hp₁]
      exact mem_singleton _
    have hsubinc : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (u : Section34VertexIndex 𝒦 𝒦'),
        Section34Incident e.1 s.1 → u.1 ⊆ e.1 → Section34Incident u.1 s.1 :=
      fun _ _ he hu => (Finset.coe_subset.mpr hu).trans he
    have hother : ∀ (e : Section34EdgeIndex 𝒦 𝒦'), Section34Incident e.1 s.1 → a.1 ⊆ e.1 →
        ∀ x ∈ section34SplitDiskImage src f₁ e, x ∈ ⋃ (u : Section34VertexIndex 𝒦 𝒦')
          (_ : Section34Incident u.1 s.1 ∧ u ≠ a), section34VertexBallImage src f₁ u := by
      intro e he hae x hx
      obtain ⟨u, u', huu, heu, hEeq⟩ := hcut.splitDiskImage_eq_inter hinj e
      have hue : u.1 ⊆ e.1 := Finset.coe_subset.mp (heu ▸ subset_union_left)
      have hu'e : u'.1 ⊆ e.1 := Finset.coe_subset.mp (heu ▸ subset_union_right)
      rw [hEeq] at hx
      by_cases hua : u = a
      · exact mem_iUnion₂.mpr ⟨u', ⟨hsubinc e u' he hu'e, fun h => huu (hua.trans h.symm)⟩,
          hx.2⟩
      · exact mem_iUnion₂.mpr ⟨u, ⟨hsubinc e u he hue, hua⟩, hx.1⟩
    set T' := ⋃ (u : Section34VertexIndex 𝒦 𝒦') (_ : Section34Incident u.1 s.1 ∧ u ≠ a),
      section34VertexBallImage src f₁ u
    have hmeetA : section34VertexBallImage src f₁ a ∩ T' ⊆
        section34SplitDiskImage src f₁ e₀ ∪ section34SplitDiskImage src f₁ e₁ := by
      rintro x ⟨hxa, hxT⟩
      obtain ⟨u, ⟨hu, hua⟩, hxu⟩ := mem_iUnion₂.mp hxT
      obtain ⟨f, hxf⟩ := hcut.exists_mem_splitDiskImage_of_ne hinj (Ne.symm hua) hxa hxu
      have haf := hcut.subset_of_mem_splitDiskImage hinj hxf hxa
      have huf := hcut.subset_of_mem_splitDiskImage hinj hxf hxu
      obtain ⟨a', b', -, hab', -⟩ := hcut.splitDiskImage_eq_inter hinj f
      have hfinc : Section34Incident f.1 s.1 := by
        change (f.1 : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
        rw [hab']
        rcases eq_or_eq_of_section34VertexIndex_subset f hab' haf with h1 | h1 <;>
          rcases eq_or_eq_of_section34VertexIndex_subset f hab' huf with h2 | h2
        · exact absurd (h2.trans h1.symm) hua
        · rw [← h1, ← h2]
          exact union_subset ha hu
        · rw [← h1, ← h2]
          exact union_subset hu ha
        · exact absurd (h2.trans h1.symm) hua
      rcases huniq f hfinc haf with h | h
      · rw [h] at hxf
        exact Or.inl hxf
      · rw [h] at hxf
        exact Or.inr hxf
    have hfinW := finite_setOf_section34Incident_graphIndex hsub (graphSkeletonSpace 𝒦) 1 s.2.1
    have hfin' : {u : Section34VertexIndex 𝒦 𝒦' | Section34Incident u.1 s.1 ∧ u ≠ a}.Finite :=
      hfinW.subset fun _ hu => hu.1
    have hT'cpt : IsCompact T' := hfin'.isCompact_biUnion fun u _ => (hVcell u).isCompact
    have hVas : section34VertexBallImage src f₁ a ⊆ (c s).source := fun x hx =>
      hTc s (mem_section34FaceTorus_iff.mpr ⟨a, ha, hx⟩)
    have hT's : T' ⊆ (c s).source := by
      intro x hx
      obtain ⟨u, ⟨hu, -⟩, hxu⟩ := mem_iUnion₂.mp hx
      exact hTc s (mem_section34FaceTorus_iff.mpr ⟨u, hu, hxu⟩)
    have hEa : ∀ e : Section34EdgeIndex 𝒦 𝒦', a.1 ⊆ e.1 →
        section34SplitDiskImage src f₁ e ⊆ section34VertexBallImage src f₁ a :=
      fun e hae x hx => hmemV e a x hx hae
    have hp₀a : p₀ ∈ section34VertexBallImage src f₁ a := hEa e₀ ha₀ (hEbdE e₀ hp₀J.2)
    have hp₁a : p₁ ∈ section34VertexBallImage src f₁ a := hEa e₁ ha₁ (hEbdE e₁ hp₁J.2)
    have hp₀T : p₀ ∈ T' := hother e₀ hi₀ ha₀ p₀ (hEbdE e₀ hp₀J.2)
    have hp₁T : p₁ ∈ T' := hother e₁ hi₁ ha₁ p₁ (hEbdE e₁ hp₁J.2)
    have hcpt : ∀ {X : Set M₂}, IsCompact X → X ⊆ (c s).source → IsClosed ((c s) '' X) :=
      fun hX hXs => (hX.image_of_continuousOn ((c s).continuousOn.mono hXs)).isClosed
    have hDcc : (c s) '' ((c s).symm '' D') = D' := by
      refine Subset.antisymm ?_ fun z hz => ⟨(c s).symm z, mem_image_of_mem _ hz,
        (c s).right_inv (hD't hz)⟩
      rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      rw [(c s).right_inv (hD't hz)]
      exact hz
    refine IsPLBall.not_subset_union_of_joined_twice (n := 2) (D := D') ⟨q, hq⟩
      (hcpt (hVcell a).isCompact hVas) (hcpt hT'cpt hT's)
      (hcpt (hcut.isPLCellOn_splitDiskImage hf₁ e₀).isCompact ((hEa e₀ ha₀).trans hVas))
      (hcpt (hcut.isPLCellOn_splitDiskImage hf₁ e₁).isCompact ((hEa e₁ ha₁).trans hVas))
      ((hcut.disjoint_splitDiskImage hinj he).image (c s).injOn
        ((hEa e₀ ha₀).trans hVas) ((hEa e₁ ha₁).trans hVas)) ?_
      (hcellA.isConnected.isPreconnected.image (c s) ((c s).continuousOn.mono
        (inter_subset_right.trans hVas))) (image_mono inter_subset_right)
      ((image_mono (inter_subset_left.trans hJD)).trans hDcc.subset)
      (hpreB.image (c s) ((c s).continuousOn.mono (inter_subset_right.trans hT's)))
      (image_mono inter_subset_right)
      ((image_mono (inter_subset_left.trans hJD)).trans hDcc.subset)
      (p₀ := (c s) p₀) (p₁ := (c s) p₁)
      ⟨⟨mem_image_of_mem _ ⟨hp₀J.1, hp₀a⟩, mem_image_of_mem _ ⟨hp₀J.1, hp₀T⟩⟩,
        mem_image_of_mem _ (hEbdE e₀ hp₀J.2)⟩
      ⟨⟨mem_image_of_mem _ ⟨hp₁J.1, hp₁a⟩, mem_image_of_mem _ ⟨hp₁J.1, hp₁T⟩⟩,
        mem_image_of_mem _ (hEbdE e₁ hp₁J.2)⟩ ?_
    · rw [← (c s).injOn.image_inter hVas hT's, ← image_union]
      exact image_mono hmeetA
    · rw [← hDcc, ← image_union]
      refine image_mono fun z hz => ?_
      obtain ⟨w, hw, hzw⟩ := hDinc z hz
      by_cases hwa : w = a
      · exact Or.inl (hwa ▸ hzw)
      · exact Or.inr (mem_iUnion₂.mpr ⟨w, ⟨hw, hwa⟩, hzw⟩)
  choose ι hι D hDcell hDS hDU using hdisk
  refine ⟨D, fun s => J s (ι s),
    fun a => J a.1.1 (ι a.1.1) ∩ section34VertexBallImage src f₁ a.1.2,
    fun a => J a.1.1 (ι a.1.1) ∩ section34VertexBallImage src f₁ a.1.2 ∩
      ⋃ e, section34SplitDiskImage src f₁ e,
    fun p => J p.1.1 (ι p.1.1) ∩ section34SplitDiskImage srcBd f₁ p.1.2,
    hDcell, hDS, hDU, fun s => (hJS s _ (hι s)).trans inter_subset_right, ?_,
    fun a => (harcs a.1.1 _ (hι a.1.1) a.1.2 a.2).1, fun _ => rfl, ?_, ?_, fun _ => rfl, ?_,
    fun _ => rfl⟩
  · intro s s' hss
    refine Set.disjoint_left.mpr fun y hy hy' => ?_
    have hyi : y ∈ interior (⋃ w, section34VertexBallImage src f₁ w) :=
      hfover s s' hss ⟨hfsub s (hDS s hy), hfsub s' (hDS s' hy')⟩
    have hyJ : y ∈ J s (ι s) := by
      rw [← hDU s]
      exact ⟨hy, interior_subset hyi⟩
    exact Set.disjoint_left.mp disjoint_interior_frontier hyi
      (((hJS s _ (hι s)).trans inter_subset_right) hyJ)
  · intro s w hw
    refine eq_empty_of_subset_empty fun y hy => ?_
    rw [← hfavoid s w hw]
    exact ⟨hfsub s (hDS s hy.1), hy.2⟩
  · intro p
    obtain ⟨x, hx⟩ := hJe p.1.1 _ (hι p.1.1) p.1.2 p.2
    have hxJ : x ∈ J p.1.1 (ι p.1.1) := by
      have hx' : x ∈ J p.1.1 (ι p.1.1) ∩ section34SplitDiskImage srcBd f₁ p.1.2 := by
        rw [hx]
        exact mem_singleton x
      exact hx'.1
    have hxc : x ∈ (c p.1.1).source := hJc _ _ (hι _) hxJ
    have hc0 : IsPLCellOn 0 ({(c p.1.1) x} : Set (EuclideanSpace ℝ (Fin 3)))
        ((fun _ : Fin 1 → ℝ => (c p.1.1) x) '' stdSimplexBoundary 0) :=
      isPLCellOn_id_of_isPLBall (isPLHomeomorphOn_const_stdSimplex_fin_one ((c p.1.1) x))
    rw [stdSimplexBoundary_zero, image_empty] at hc0
    have hcell := hc0.image_chart_symm (hc p.1.1)
      (singleton_subset_iff.mpr ((c p.1.1).map_source hxc))
    rw [image_singleton, (c p.1.1).left_inv hxc, image_empty] at hcell
    change IsPLCellOn 0 (J p.1.1 (ι p.1.1) ∩ section34SplitDiskImage srcBd f₁ p.1.2) ∅
    rw [hx]
    exact hcell
  · intro s e he
    obtain ⟨a, b, -, hab, hEeq⟩ := hcut.splitDiskImage_eq_inter hinj e
    have hn : ¬ Section34Incident a.1 s.1 ∨ ¬ Section34Incident b.1 s.1 := by
      by_cases ha : Section34Incident a.1 s.1
      · refine Or.inr fun hb => he ?_
        change (e.1 : Set Ea) ⊆ convexHull ℝ (s.1 : Set Ea)
        rw [hab]
        exact union_subset ha hb
      · exact Or.inl ha
    refine eq_empty_of_subset_empty fun y hy => ?_
    have hyE : y ∈ section34SplitDiskImage src f₁ e := hEbdE e hy.2
    rw [hEeq] at hyE
    have hyf : y ∈ fbl s := hJf s _ (hι s) hy.1
    rcases hn with hn | hn
    · rw [← hfavoid s a hn]
      exact ⟨hyf, hyE.1⟩
    · rw [← hfavoid s b hn]
      exact ⟨hyf, hyE.2⟩

end Diagram

end DifferentialGeometry.Topology.PiecewiseLinear
