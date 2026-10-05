import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.Normalization.Termination
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.CellDecomposition.Homeomorph
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceHomology
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceDisks
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSourceFaceOrder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonSlide
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCompressionLeaf
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualBalls
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutAndGraph
import DifferentialGeometry.Topology.PiecewiseLinear.Approximation.Normalization.NormalForm

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPLHomeomorphOn_dist_lt_on_neighborhood
    (C V : Set (EuclideanSpace ℝ (Fin 3))) (hC : IsPLBall 3 C)
    (hV : IsOpen V) (hCV : C ⊆ V)
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hh : Topology.IsEmbedding (V.domRestrict h)) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn f C (f '' C) ∧ ∀ x ∈ C, dist (f x) (h x) < ε := by
  classical
  obtain ⟨K, K', src, srcBd, H, f₁, hcut, hcar, hgraph⟩ :=
    exists_compactCutAndGraph hC hV hCV hh hε
  have hgen := hgraph.carriesFundamentalGroupOnto
  obtain ⟨env, henv⟩ := exists_compactFaceEnvelopes hV hCV hh hcut hcar hgraph
  obtain ⟨fbl₀, fblBd₀, hfam₀⟩ := exists_compactFaceShellBalls hV hCV hh hcut henv
  obtain ⟨fbl₁, fblBd₁, hfam₁, hgp₁, hgp₂, hfin₁, hfin₂⟩ :=
    exists_compactFaceBallsGeneralPosition hcut hgraph henv hfam₀
  obtain ⟨-, hKfin, hK'fin, -, -, -, hscell, hsbd, hsinter, hsdim, hscover, -, -, -, -, -, -,
    -, htetra, -, -, -, -, hparent, -, -, hends, -, -⟩ := id hcut
  obtain ⟨hcarS, hcarDiam, -⟩ := id hcar
  obtain ⟨-, hf₁, -, -, -, -, -, -, -, hcarV, -⟩ := id hgraph
  obtain ⟨-, -, henvAvoid, henvOverlap, henvCar, -, henvExt⟩ := id henv
  have hrim : ∀ s : Section34CompactSimplexIndex K 3,
      h '' section34CompactSimplexRim s.1 ⊆ interior (fbl₁ s) := fun s =>
    (image_mono (section34CompactSimplexRim_subset s.1)).trans (hfam₁ s).2.1
  have hinv₁ : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl₁ fblBd₁ := by
    refine ⟨fun s => (hfam₁ s).1, hrim, fun s w hw => ?_, fun s s' hss => ?_, hgp₁, hgp₂,
      fun s => ?_, hfin₁, hfin₂, fun s t hst => ?_, ?_⟩
    · exact eq_empty_of_subset_empty
        ((inter_subset_inter_left _ (hfam₁ s).2.2).trans (henvAvoid s w hw).subset)
    · exact (inter_subset_inter (hfam₁ s).2.2 (hfam₁ s').2.2).trans (henvOverlap s s' hss)
    · exact compactTraceHomology hgraph henv s (hgen s) (hfam₁ s).1 (hrim s)
        (hfam₁ s).2.2
    · exact (hfam₁ s).2.2.trans (henvCar s t hst)
    · exact section34CompactExterior_mono (fun s => (hfam₁ s).2.2.trans subset_closure) henvExt
  obtain ⟨fbl, fblBd, hinv, hnc, hnb⟩ :=
    exists_face_ball_family_without_admissible_moves (tgtVBd := section34CompactVertexBallImage srcBd f₁)
      (tgtE := section34CompactSplitDiskImage src f₁) hKfin hinv₁
      (fun _ _ s hg hop => by
        obtain ⟨g', gBd', hinv', hoff, hc, hp⟩ :=
          exists_compactCompression hcut hcar hgraph hg s hop
        exact ⟨g', gBd', hinv', hoff, section34CompactFaceBallRank_lt_of_compression hc hp⟩)
      (fun _ _ s hg hop => by
        obtain ⟨g', gBd', hinv', hoff, hc, hp⟩ :=
          exists_compactBigonSlide hcut hcar hgraph hg s hop
        exact ⟨g', gBd', hinv', hoff, section34CompactFaceBallRank_lt_of_bigonSlide hc hp⟩)
  have htrace := isCompactMeridionalFaceTraceFamily_of_no_admissible_moves hcut hgraph hinv hnc hnb
  obtain ⟨tgtD, tgtDBd, tgtA, tgtABd, tgtP, hdisk⟩ :=
    exists_compactFaceDisks hcut hgraph hinv htrace
  obtain ⟨tgtR, tgtRBd, tgtX, tgtXBd, tgtI, tgtIBd, tgtO, tgtOBd, tgtQ, tgtQBd, hres⟩ :=
    exists_compactResidualBalls hcut hcar hgraph hinv htrace hdisk
  have hface := compactSourceFace_iff_cutLe hcut
  set tc : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)) :=
    section34BoundedCell (section34CompactVertexBallImage src f₁) tgtR
      (section34CompactSplitDiskImage src f₁) tgtD tgtX tgtA tgtI tgtP tgtO tgtQ with htcdef
  set tcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3)) :=
    section34BoundedCell (section34CompactVertexBallImage srcBd f₁) tgtRBd
      (section34CompactSplitDiskImage srcBd f₁) tgtDBd tgtXBd tgtABd tgtIBd (fun _ => ∅)
      tgtOBd tgtQBd with htcbddef
  obtain ⟨htbd, htinter⟩ :=
    compactTargetRecognition hcut hgraph hdisk hres hface tc tcBd htcdef htcbddef
  obtain ⟨hDcell, -, -, -, -, hAcell, -, -, hPcell, -, -, -⟩ := id hdisk
  obtain ⟨hRcell, hXcell, hIcell, hOcell, hQcell, -, -, -, -, -, -, -, -, -, -, -, -, hresCar,
    -, -, -, -, -, -⟩ := id hres
  have hsubV : ∀ w : Section34CompactVertexIndex K K',
      src (.vertexBall w) ⊆ section34CompactCutNeighborhood src := fun w =>
    subset_iUnion (fun v : Section34CompactVertexIndex K K' => src (.vertexBall v)) w
  have hsubE : ∀ e : Section34CompactEdgeIndex K K',
      src (.splitDisk e) ⊆ section34CompactCutNeighborhood src := by
    intro e
    obtain ⟨w, w', -, -, heq⟩ := hends e
    rw [heq]
    exact inter_subset_left.trans (hsubV w)
  have hVcell : ∀ w, IsPLCellOn 3 (section34CompactVertexBallImage src f₁ w)
      (section34CompactVertexBallImage srcBd f₁ w) := fun w =>
    (hscell (.vertexBall w)).image (isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset hf₁
      (hscell (.vertexBall w)).isPolyhedron (hsubV w))
  have hEcell : ∀ e, IsPLCellOn 2 (section34CompactSplitDiskImage src f₁ e)
      (section34CompactSplitDiskImage srcBd f₁ e) := fun e =>
    (hscell (.splitDisk e)).image (isPLHomeomorphInto_of_isPLHomeomorphOn_of_subset hf₁
      (hscell (.splitDisk e)).isPolyhedron (hsubE e))
  have htcell : ∀ l, IsPLCellOn (section34BoundedDim l) (tc l) (tcBd l) := by
    intro l
    cases l with
    | vertexBall w => exact hVcell w
    | tetraBall t => exact hRcell t
    | splitDisk e => exact hEcell e
    | faceDisk s => exact hDcell s
    | patch x => exact hXcell x
    | faceArc a => exact hAcell a
    | edgeArc i => exact hIcell i
    | markedPoint p => exact hPcell p
    | outerFace o => exact hOcell o
    | outerArc q => exact hQcell q
  obtain ⟨F, hF, hFim⟩ := exists_isPLHomeomorphInto_of_graph_cut_cells hKfin hK'fin hscell hsbd
    hsinter hsdim htcell htbd htinter
  have hCsub : C ⊆ ⋃ l, src l := by
    rw [hscover]
    exact subset_union_left
  have hdist : ∀ x ∈ C, dist (F x) (h x) < ε := by
    intro x hx
    obtain ⟨l, hl⟩ := mem_iUnion.mp (hCsub hx)
    obtain ⟨m, hm3, hlm⟩ := hparent l
    have hFx : F x ∈ tc m := by
      have h1 : F x ∈ tc l := hFim l ▸ mem_image_of_mem F hl
      have h2 : tc l ⊆ tc m := by
        intro y hy
        have hmem : y ∈ ⋃ k ∈ section34Face src l ∩ section34Face src m, tc k :=
          mem_iUnion₂.mpr ⟨l, ⟨Subset.rfl, hlm⟩, hy⟩
        rw [← htinter l m] at hmem
        exact hmem.2
      exact h2 h1
    have hhx : h x ∈ h '' src m := ⟨x, hlm hl, rfl⟩
    rcases section34BoundedDim_eq_three hm3 with ⟨w, rfl⟩ | ⟨t, rfl⟩
    · obtain ⟨t₀, ht₀, hwt₀⟩ := exists_face_of_section34CompactVertexIndex w
      have hcarw := hcarV w t₀ ht₀ hwt₀
      exact hcarDiam t₀ ht₀ (F x) (interior_subset (hcarw (Or.inr hFx))) (h x)
        (interior_subset (hcarw (Or.inl hhx)))
    · have hQt : src (.tetraBall t) ⊆ convexHull ℝ (t.1 : Set (EuclideanSpace ℝ (Fin 3))) := by
        rw [htetra t]
        exact closure_minimal sdiff_subset (t.1.finite_toSet.isClosed_convexHull ℝ)
      have hstar : convexHull ℝ (t.1 : Set (EuclideanSpace ℝ (Fin 3))) ⊆
          section34CompactCarrierSupport K t.1 := by
        obtain ⟨w, hw⟩ : ∃ w, w ∈ t.1 := Finset.card_pos.mp (by rw [t.2.2]; norm_num)
        intro y hy
        exact mem_iUnion₂.mpr ⟨w, Finset.mem_coe.mpr hw, mem_iUnion₂.mpr ⟨t.1, ⟨t.2.1, hw⟩, hy⟩⟩
      exact hcarDiam t.1 t.2.1 (F x) (hresCar t hFx) (h x)
        (interior_subset (hcarS t.1 t.2.1 ⟨x, hstar (hQt (hlm hl)), rfl⟩))
  have hpl : IsPiecewiseAffineOn F C :=
    (isPLOn_iff_isPiecewiseAffineOn.mp hF.isPLOn).mono_of_isPolyhedron hC.isPolyhedron hCsub
  exact ⟨F, isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hC.isPolyhedron hpl
    (hF.injOn.mono hCsub).bijOn_image, hdist⟩

theorem exists_isPLHomeomorphOn_dist_lt_of_isPLBall_three
    (C : Set (EuclideanSpace ℝ (Fin 3))) (hC : IsPLBall 3 C)
    (h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hcont : ContinuousOn h C) (hinj : InjOn h C) (ε : ℝ) (hε : 0 < ε) :
    ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphOn f C (f '' C) ∧ ∀ x ∈ C, dist (f x) (h x) < ε := by
  obtain ⟨p, hp, hpC, hpdist⟩ := exists_isPLBall_subset_interior_dist_lt hC hcont (half_pos hε)
  have hpball : IsPLBall 3 (p '' C) := hC.of_isPLHomeomorphOn hp
  have hemb := isEmbedding_domRestrict_interior_of_continuousOn_injOn
    hC.isPolyhedron.isCompact hcont hinj
  obtain ⟨g, hg, hgdist⟩ := exists_isPLHomeomorphOn_dist_lt_on_neighborhood (p '' C) (interior C) hpball
    isOpen_interior hpC h hemb (ε / 2) (half_pos hε)
  refine ⟨g ∘ p, ?_, fun x hx => ?_⟩
  · rw [image_comp]
    exact hp.trans hg
  · calc dist ((g ∘ p) x) (h x)
        ≤ dist (g (p x)) (h (p x)) + dist (h (p x)) (h x) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hgdist _ ⟨x, hx, rfl⟩) (hpdist x hx)
      _ = ε := add_halves ε

end DifferentialGeometry.Topology.PiecewiseLinear
