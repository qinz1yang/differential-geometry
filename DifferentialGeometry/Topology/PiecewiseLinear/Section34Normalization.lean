/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.External.CanonicalTopology.Topology.Homology.Integral
import DifferentialGeometry.Topology.PiecewiseLinear.IsPLHomeomorphIntoMonoOfIsPLCellOn
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Frame
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SplitDiskIntersection
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Statements
import DifferentialGeometry.Topology.PiecewiseLinear.TameNestedCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBallVocabulary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TerminalFaceBalls
import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceBalls
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BigonSlide
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionLeaf
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TraceNormalization
import DifferentialGeometry.Topology.PiecewiseLinear.ControlledGraphNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Control

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]
  {U : Set M₁} {h : M₁ → M₂} {η : M₁ → ℝ} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁} {H : Finset Ea → Set M₂}
  {cr : Section34VertexIndex 𝒦 𝒦' → Finset Ea} {f₁ : M₁ → M₂}

omit [FiniteDimensional ℝ Ea] in
theorem simplexBody_subset_of_mem_faces {t : Finset Ea} (ht : t ∈ 𝒦.complex.faces) :
    simplexBody 𝒦 t ⊆ U := by
  rintro _ ⟨x, hx, rfl⟩
  exact 𝒦.bijOn.mapsTo (𝒦.complex.convexHull_subset_space ht hx)

omit [FiniteDimensional ℝ Ea] in
theorem graphSkeletonSpace_subset (𝒦 : LocallyFinitePLPieceIn Ea 3 M₁ U) :
    graphSkeletonSpace 𝒦 ⊆ U := by
  simp only [graphSkeletonSpace]
  exact iUnion₂_subset fun _ ht => simplexBody_subset_of_mem_faces ht.1

omit [FiniteDimensional ℝ Ea] in
theorem nonempty_simplexRim {t : Finset Ea} (ht : 2 ≤ t.card) : (simplexRim 𝒦 t).Nonempty := by
  obtain ⟨v, hv⟩ : ∃ v, v ∈ t := Finset.card_pos.mp (by omega)
  have hne : ({v} : Finset Ea) ≠ t := by
    intro hEq
    have hcard := congrArg Finset.card hEq
    simp only [Finset.card_singleton] at hcard
    omega
  refine ⟨𝒦.map v, ?_⟩
  simp only [simplexRim, mem_iUnion₂]
  exact ⟨{v}, lt_of_le_of_ne (Finset.singleton_subset_iff.mpr hv) hne,
    ⟨v, subset_convexHull ℝ _ (by simp), rfl⟩⟩

omit [FiniteDimensional ℝ Ea] in
theorem nonempty_section34FaceTorus
    (hgraph : Section34GraphFrame U U h η H 𝒦 𝒦' src cr f₁) (s : Section34SimplexIndex 𝒦 3) :
    (section34FaceTorus (section34VertexBallImage src f₁) s).Nonempty := by
  obtain ⟨-, -, -, -, -,
    -, -, -, hrim, -,
    -, -, -, -⟩ := id hgraph
  have hcard : 2 ≤ s.1.card := by
    have hc := s.2.2
    omega
  obtain ⟨x, hx⟩ := nonempty_simplexRim (𝒦 := 𝒦) hcard
  exact ⟨h x, interior_subset (hrim s ⟨x, hx, rfl⟩)⟩

end Leaves

def Section34NormalFamilyStatement : Prop :=
  ∀ {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
    [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
    {η : M₁ → ℝ} [Nonempty M₁] [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)]
    [HasGroupoid M₂ (plGroupoid 3)], IsOpen U → Topology.IsEmbedding (U.domRestrict h) →
    ContinuousOn η U → (∀ x ∈ U, 0 < η x) →
    ∃ (N : ℕ) (𝒦 𝒦' : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin N)) 3 M₁ U)
      (src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁)
      (H : Finset (EuclideanSpace ℝ (Fin N)) → Set M₂)
      (cr : Section34VertexIndex 𝒦 𝒦' → Finset (EuclideanSpace ℝ (Fin N))) (f₁ : M₁ → M₂)
      (tgtV tgtVBd : Section34VertexIndex 𝒦 𝒦' → Set M₂)
      (tgtE tgtEBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
      (fbl fblBd : Section34SimplexIndex 𝒦 3 → Set M₂),
      Section34NormalPlus U h η 𝒦 𝒦' src srcBd H cr f₁ tgtV tgtVBd tgtE tgtEBd fbl fblBd

theorem section34NormalFamily (hP0 : Section34ControlStatement.{u})
    (h351 : ControlledGraphNeighborhoodStatement.{u}) : Section34NormalFamilyStatement.{u} := by
  intro M₁ M₂ _ _ _ _ U h η _ _ _ _ _ _ hU hh hηc hηpos
  obtain ⟨N, 𝒦, H, hcm, hctrl⟩ := hP0 hU hh η hηc hηpos
  obtain ⟨𝒦', src, srcBd, cr, f₁, hcut, hgraph⟩ :=
    h351 hU hh (EuclideanSpace ℝ (Fin N)) 𝒦 hcm η H hctrl hU
      (graphSkeletonSpace_subset 𝒦) Subset.rfl η hηc hηpos
  obtain ⟨-, -, hpl, -, -,
    -, -, -, -, -,
    -, -, -, -⟩ := id hgraph
  obtain ⟨-, -, -, hcell, hbd,
    -, -, -, -, -,
    -, -, -, -, -,
    -, -, -, -, hsupT,
    -, -, hends, -, -⟩ := id hcut
  obtain ⟨hsup, -, -, -, -, -⟩ := id hctrl
  obtain ⟨fbl₀, fblBd₀, hinv₀⟩ := exists_section34FaceBalls hU hh hcut hctrl hgraph
  obtain ⟨fbl, fblBd, hinv, hnc, hnb⟩ :=
    exists_section34TerminalFaceBalls hinv₀
      (fun _ _ s hg hop => by
        obtain ⟨g', gBd', hinv', hoff, hc, hp⟩ :=
          exists_section34Compression hU hh hcut hctrl hgraph hg s hop
        exact ⟨g', gBd', hinv', hoff, section34FaceBallRank_lt_of_compression hc hp⟩)
      (fun _ _ s hg hop => by
        obtain ⟨g', gBd', hinv', hoff, hc, hp⟩ :=
          exists_section34BigonSlide hU hh hcut hctrl hgraph hg s hop
        exact ⟨g', gBd', hinv', hoff, section34FaceBallRank_lt_of_bigonSlide hc hp⟩)
  obtain ⟨hfblcell, -, hfblV, hfblfbl, -, -, -, -, -, hext⟩ := id hinv
  have htrace := section34Trace_of_noOperation hU hh hcut hgraph hinv hnc hnb
  have hsubV : ∀ w : Section34VertexIndex 𝒦 𝒦',
      src (Section34Label.vertexBall w) ⊆ section34CutNeighborhood src := by
    intro w
    simp only [section34CutNeighborhood]
    exact subset_iUnion
      (fun v : Section34VertexIndex 𝒦 𝒦' => src (Section34Label.vertexBall v)) w
  have hsubE : ∀ e : Section34EdgeIndex 𝒦 𝒦',
      src (Section34Label.splitDisk e) ⊆ section34CutNeighborhood src := by
    intro e
    obtain ⟨w, w', -, -, heq⟩ := hends e
    rw [heq]
    exact inter_subset_left.trans (hsubV w)
  have hVcell : ∀ w, IsPLCellOn 3 (section34VertexBallImage src f₁ w)
      (section34VertexBallImage srcBd f₁ w) := fun w =>
    (hcell (Section34Label.vertexBall w)).image
      (hpl.mono_of_isPLCellOn (hcell (Section34Label.vertexBall w)) (hsubV w))
  have hEcell : ∀ e, IsPLCellOn 2 (section34SplitDiskImage src f₁ e)
      (section34SplitDiskImage srcBd f₁ e) := fun e =>
    (hcell (Section34Label.splitDisk e)).image
      (hpl.mono_of_isPLCellOn (hcell (Section34Label.splitDisk e)) (hsubE e))
  have hEV : ∀ (e : Section34EdgeIndex 𝒦 𝒦') (w : Section34VertexIndex 𝒦 𝒦'),
      src (Section34Label.splitDisk e) ⊆ src (Section34Label.vertexBall w) →
        section34SplitDiskImage src f₁ e ⊆ section34VertexBallImage srcBd f₁ w := by
    intro e w hsube
    simp only [section34SplitDiskImage, section34VertexBallImage]
    refine image_mono ?_
    rw [hbd (Section34Label.vertexBall w)]
    exact subset_biUnion_of_mem (u := src)
      (show Section34Label.splitDisk e ∈
        section34Face src (Section34Label.vertexBall w) \ {Section34Label.vertexBall w} from
        ⟨hsube, by simp⟩)
  have hVV : ∀ w w' : Section34VertexIndex 𝒦 𝒦', w ≠ w' →
      section34VertexBallImage src f₁ w ∩ section34VertexBallImage src f₁ w' ⊆
        ⋃ e, section34SplitDiskImage src f₁ e := by
    intro w w' hww
    simp only [section34VertexBallImage, section34SplitDiskImage]
    rintro y ⟨⟨a, ha, rfl⟩, b, hb, hab⟩
    have hEq : b = a := hpl.injOn (hsubV w' hb) (hsubV w ha) hab
    have hb' : a ∈ src (Section34Label.vertexBall w') := hEq ▸ hb
    obtain ⟨e, he⟩ := exists_splitDisk_src_eq_inter_vertexBall hcut hww ⟨a, ha, hb'⟩
    exact mem_iUnion.mpr ⟨e, a, by rw [he]; exact ⟨ha, hb'⟩, rfl⟩
  have htetraH : ∀ t : Section34SimplexIndex 𝒦 4,
      h '' src (Section34Label.tetraBall t) ⊆ H t.1 := fun t =>
    (image_mono (hsupT t)).trans ((hsup t.1 t.2.1).trans interior_subset)
  exact ⟨N, 𝒦, 𝒦', src, srcBd, H, cr, f₁, section34VertexBallImage src f₁,
    section34VertexBallImage srcBd f₁, section34SplitDiskImage src f₁,
    section34SplitDiskImage srcBd f₁, fbl, fblBd, hcut, hctrl, hgraph, hext, htrace,
    fun _ => rfl, fun _ => rfl, hVcell, hEcell, hEV, hVV, htetraH, hfblcell, hfblV, hfblfbl,
    fun s w Dj Jd h1 h2 h3 h4 h5 h6 => hnc s ⟨w, Dj, Jd, h1, h2, h3, h4, h5, h6⟩,
    fun s w e B B' Bb Dj Jd h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 =>
      hnb s ⟨w, e, B, B', Bb, Dj, Jd, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩⟩

theorem section34NormalFamilyStatement : Section34NormalFamilyStatement.{u} :=
  section34NormalFamily section34Control controlledGraphNeighborhoodStatement

end DifferentialGeometry.Topology.PiecewiseLinear
