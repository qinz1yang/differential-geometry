/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral
import DifferentialGeometry.Topology.PiecewiseLinear.CellMapTriangulation
import DifferentialGeometry.Topology.PiecewiseLinear.ControlledInwardPush
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.TameNestedCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceEnvelopes
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceHomology
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSplitDiskIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactFaceDisks
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTargetRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactSourceFaceOrder
import DifferentialGeometry.Topology.PiecewiseLinear.Section33TubeApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactBigonSlide
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCompressionLeaf
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualBalls
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCutAndGraph
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactTraceNormalization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe v

section Leaves

variable {C V : Set (EuclideanSpace ℝ (Fin 3))}
  {h f₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)} {ε : ℝ}
  {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {env : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}

end Leaves

section Descent

variable {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3)}
  {H : Finset (EuclideanSpace ℝ (Fin 3)) → Set (EuclideanSpace ℝ (Fin 3))}
  {tgtV tgtVBd : Section34CompactVertexIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}
  {tgtE tgtEBd : Section34CompactEdgeIndex K K' → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactTerminalFaceBalls (hK : K.faces.Finite)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3))}
    (hinv : Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl fblBd)
    (hcomp : ∀ (g gBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
      (s : Section34CompactSimplexIndex K 3),
      Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g gBd →
      Section34CompactCompression K K' tgtVBd tgtE g gBd s →
      ∃ g' gBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
        Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g' gBd' ∧
        (∀ s', s' ≠ s → g' s' = g s' ∧ gBd' s' = gBd s') ∧
        section34CompactFaceBallRank tgtV tgtEBd gBd' s <
          section34CompactFaceBallRank tgtV tgtEBd gBd s)
    (hslide : ∀ (g gBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
      (s : Section34CompactSimplexIndex K 3),
      Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g gBd →
      Section34CompactBigonSlide K K' tgtV tgtVBd tgtE tgtEBd gBd s →
      ∃ g' gBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
        Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g' gBd' ∧
        (∀ s', s' ≠ s → g' s' = g s' ∧ gBd' s' = gBd s') ∧
        section34CompactFaceBallRank tgtV tgtEBd gBd' s <
          section34CompactFaceBallRank tgtV tgtEBd gBd s) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
      Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl' fblBd' ∧
      (∀ s, ¬ Section34CompactCompression K K' tgtVBd tgtE fbl' fblBd' s) ∧
      ∀ s, ¬ Section34CompactBigonSlide K K' tgtV tgtVBd tgtE tgtEBd fblBd' s := by
  classical
  have hfin := finite_section34CompactSimplexIndex hK 3
  let _ : Fintype (Section34CompactSimplexIndex K 3) := Fintype.ofFinite _
  have hdrop : ∀ (gBd gBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)))
      (s : Section34CompactSimplexIndex K 3), (∀ s', s' ≠ s → gBd' s' = gBd s') →
      section34CompactFaceBallRank tgtV tgtEBd gBd' s <
        section34CompactFaceBallRank tgtV tgtEBd gBd s →
      ∑ s', section34CompactFaceBallRank tgtV tgtEBd gBd' s' <
        ∑ s', section34CompactFaceBallRank tgtV tgtEBd gBd s' := by
    intro gBd gBd' s hoff hlt
    refine Finset.sum_lt_sum (fun s' _ => ?_) ⟨s, Finset.mem_univ s, hlt⟩
    by_cases hs : s' = s
    · subst hs
      exact hlt.le
    · exact (section34CompactFaceBallRank_congr (hoff s' hs)).le
  suffices key : ∀ n : ℕ,
      ∀ g gBd : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
        ∑ s', section34CompactFaceBallRank tgtV tgtEBd gBd s' = n →
        Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd g gBd →
        ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set (EuclideanSpace ℝ (Fin 3)),
          Section34CompactFaceBallInvariants K K' h H tgtV tgtEBd fbl' fblBd' ∧
          (∀ s, ¬ Section34CompactCompression K K' tgtVBd tgtE fbl' fblBd' s) ∧
          ∀ s, ¬ Section34CompactBigonSlide K K' tgtV tgtVBd tgtE tgtEBd fblBd' s from
    key _ fbl fblBd rfl hinv
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro g gBd hn hg
    by_cases hc : ∃ s, Section34CompactCompression K K' tgtVBd tgtE g gBd s
    · obtain ⟨s, hs⟩ := hc
      obtain ⟨g', gBd', hinv', hoff, hlt⟩ := hcomp g gBd s hg hs
      exact ih _ (hn ▸ hdrop gBd gBd' s (fun s' hs' => (hoff s' hs').2) hlt) g' gBd' rfl hinv'
    · by_cases hb : ∃ s, Section34CompactBigonSlide K K' tgtV tgtVBd tgtE tgtEBd gBd s
      · obtain ⟨s, hs⟩ := hb
        obtain ⟨g', gBd', hinv', hoff, hlt⟩ := hslide g gBd s hg hs
        exact ih _ (hn ▸ hdrop gBd gBd' s (fun s' hs' => (hoff s' hs').2) hlt) g' gBd' rfl
          hinv'
      · exact ⟨g, gBd, hg, not_exists.mp hc, not_exists.mp hb⟩

end Descent

section Extension

variable {K K' : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin 3))}
  {src srcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}

theorem exists_compactApproximation_of_cellDiagram (hK : K.faces.Finite)
    (hK' : K'.faces.Finite)
    (hsc : ∀ l, IsPLCellOn (section34BoundedDim l) (src l) (srcBd l))
    (hsbd : ∀ l, srcBd l = ⋃ m ∈ section34Face src l \ {l}, src m)
    (hsinter : ∀ l m, src l ∩ src m = ⋃ k ∈ section34Face src l ∩ section34Face src m, src k)
    (hsdim : ∀ l m, src m ⊆ src l → m = l ∨ section34BoundedDim m < section34BoundedDim l)
    {tc tcBd : Section34CompactLabelOf K K' → Set (EuclideanSpace ℝ (Fin 3))}
    (htcell : ∀ l, IsPLCellOn (section34BoundedDim l) (tc l) (tcBd l))
    (htbd : ∀ l, tcBd l = ⋃ m ∈ section34Face src l \ {l}, tc m)
    (htinter : ∀ l m, tc l ∩ tc m = ⋃ k ∈ section34Face src l ∩ section34Face src m, tc k) :
    ∃ F : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      IsPLHomeomorphInto 3 F (⋃ l, src l) ∧ ∀ l, F '' src l = tc l := by
  have hfin := finite_section34CompactLabelOf hK hK'
  choose Pp rr uu hrr huu hsceq hsbdeq using hsc
  choose Qq ss vv hss hvv htceq htbdeq using htcell
  refine exists_isPLHomeomorphInto_of_labelledCells section34BoundedDim (section34Face src) Pp Qq
    rr ss uu vv src tc section34BoundedDim_le_three hrr hss huu hvv hsceq htceq
    (fun l m hm => hsdim l m hm) ?_ ?_ hsinter htinter ?_ ?_
  · intro l
    rw [← hsbdeq l]
    exact hsbd l
  · intro l
    rw [← htbdeq l]
    exact htbd l
  · intro x _
    exact ⟨univ, Filter.univ_mem, Set.toFinite _⟩
  · intro y _
    exact ⟨univ, Filter.univ_mem, Set.toFinite _⟩

end Extension

def Moise341OnNeighborhood : Prop :=
  ∀ (C V : Set (EuclideanSpace ℝ (Fin 3))), IsPLBall 3 C → IsOpen V → C ⊆ V →
    ∀ h : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
      Topology.IsEmbedding (V.domRestrict h) →
    ∀ ε : ℝ, 0 < ε →
      ∃ f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3),
        IsPLHomeomorphOn f C (f '' C) ∧ ∀ x ∈ C, dist (f x) (h x) < ε

theorem moise341OnNeighborhood (h331 : Moise331OnTube) :
    Moise341OnNeighborhood := by
  classical
  intro C V hC hV hCV h hh ε hε
  obtain ⟨K, K', src, srcBd, H, f₁, hcut, hcar, hgraph⟩ :=
    exists_compactCutAndGraph h331 hC hV hCV hh hε
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
    exists_compactTerminalFaceBalls (tgtVBd := section34CompactVertexBallImage srcBd f₁)
      (tgtE := section34CompactSplitDiskImage src f₁) hKfin hinv₁
      (fun _ _ s hg hop => by
        obtain ⟨g', gBd', hinv', hoff, hc, hp⟩ :=
          exists_compactCompression hcut hcar hgraph hg s hop
        exact ⟨g', gBd', hinv', hoff, section34CompactFaceBallRank_lt_of_compression hc hp⟩)
      (fun _ _ s hg hop => by
        obtain ⟨g', gBd', hinv', hoff, hc, hp⟩ :=
          exists_compactBigonSlide hcut hcar hgraph hg s hop
        exact ⟨g', gBd', hinv', hoff, section34CompactFaceBallRank_lt_of_bigonSlide hc hp⟩)
  have htrace := compactTrace_of_noOperation hcut hgraph hinv hnc hnb
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
  obtain ⟨F, hF, hFim⟩ := exists_compactApproximation_of_cellDiagram hKfin hK'fin hscell hsbd
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

theorem moise341_of_onNeighborhood (h331 : Moise331OnTube) : Moise341 := by
  intro C hC h hcont hinj ε hε
  obtain ⟨p, hp, hpC, hpdist⟩ := exists_isPLBall_subset_interior_dist_lt hC hcont (half_pos hε)
  have hpball : IsPLBall 3 (p '' C) := hC.of_isPLHomeomorphOn hp
  have hemb := isEmbedding_domRestrict_interior_of_continuousOn_injOn
    hC.isPolyhedron.isCompact hcont hinj
  obtain ⟨g, hg, hgdist⟩ := moise341OnNeighborhood h331 (p '' C) (interior C) hpball
    isOpen_interior hpC h hemb (ε / 2) (half_pos hε)
  refine ⟨g ∘ p, ?_, fun x hx => ?_⟩
  · rw [image_comp]
    exact hp.trans hg
  · calc dist ((g ∘ p) x) (h x)
        ≤ dist (g (p x)) (h (p x)) + dist (h (p x)) (h x) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hgdist _ ⟨x, hx, rfl⟩) (hpdist x hx)
      _ = ε := add_halves ε

end DifferentialGeometry.Topology.PiecewiseLinear
