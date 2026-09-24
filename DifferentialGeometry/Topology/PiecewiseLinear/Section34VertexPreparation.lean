/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34EdgeEnds
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercedVertexCells
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingCircleNeighborhoods
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ChartLocalEnlargements
import DifferentialGeometry.Topology.PiecewiseLinear.Section34GraphCores
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LensImages
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LensIsolation
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnStabilityScales
import DifferentialGeometry.Topology.PiecewiseLinear.Section34LocalMargins
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeparationMargins
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SplitDiskNeighborhoods
import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularGenerators
import DifferentialGeometry.Topology.PiecewiseLinear.Section34MarkedNestedAnnuli

/-! # Section34Vertex Preparation -/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Leaves

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U W : Set M₁} {h : M₁ → M₂}
  {η ψ : M₁ → ℝ} {H : Finset Ea → Set M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ (EuclideanSpace ℝ (Fin 3))}
  {Sd : Section34SimplexIndex 𝒦 3 → Set (EuclideanSpace ℝ (Fin 3))}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34VertexPreparation [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQint : ∀ w, h '' src (Section34Label.vertexBall w) ⊆ interior (Q w))
    (hCchart : ∀ w : Section34VertexIndex 𝒦 𝒦', ∃ c ∈ (plGroupoid 3).maximalAtlas M₂,
      h '' src (Section34Label.vertexBall w) ⊆ c.source) :
    ∃ (Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁)
      (ends : Section34EdgeIndex 𝒦 𝒦' →
        Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦')
      (Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁)
      (ε : Section34VertexIndex 𝒦 𝒦' → ℝ),
      Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
        Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε := by
  let _ := (inferInstance : SecondCountableTopology M₂)
  let _ := (inferInstance : HasGroupoid M₂ (plGroupoid 3))
  let _ := (inferInstance : FiniteDimensional ℝ Ea)
  obtain ⟨ends, hends⟩ := exists_section34_edge_ends hframe
  obtain ⟨diskO, hdiskO⟩ := exists_section34_splitDisk_neighborhoods hU hh hframe
  obtain ⟨Cc, hcc, hsrcCc, hCcU, hQ, hchart, hLFU⟩ :=
    exists_section34_chart_local_enlargements hU
      (continuousOn_iff_continuous_domRestrict.mpr hh.continuous) hframe hQint hCchart
  let CcBd := fun w => frontier (Cc w)
  have hLF : ∀ x ∈ ⋃ w, Cc w, ∃ V ∈ 𝓝 x, {w | (Cc w ∩ V).Nonempty}.Finite := by
    intro x hx
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    exact hLFU x (hCcU w hw)
  have hCcLF : LocallyFinite fun w => {x : U | (x : M₁) ∈ Cc w} := by
    intro x
    obtain ⟨V, hV, hfin⟩ := hLFU x x.2
    refine ⟨Subtype.val ⁻¹' V, continuous_subtype_val.continuousAt hV, hfin.subset ?_⟩
    rintro w ⟨y, hyC, hyV⟩
    exact ⟨y, hyC, hyV⟩
  obtain ⟨Cp, hcp, hcircle, hnonadj, hCpCc, hcover, hCpLF, hlensO, -, hcross, hvertex, hvdisj⟩ :=
    exists_section34_crossing_pierced_vertex_cells hU hframe hN ends hends Cc hsrcCc hCcLF
      diskO hdiskO.1 hdiskO.2.1 hdiskO.2.2.2.2
  let CpBd := fun w => frontier (Cp w)
  have hsub : ∀ w, src (.vertexBall w) ⊆ Cc w ∧ Cp w ⊆ Cc w ∧ Cc w ⊆ U :=
    fun w => ⟨(hsrcCc w).trans interior_subset, (hCpCc w).trans interior_subset, hCcU w⟩
  have hlens (e d) (hed : e ≠ d) : Disjoint (Cp (ends e).1 ∩ Cp (ends e).2)
      (Cp (ends d).1 ∩ Cp (ends d).2) :=
    (hdiskO.2.2.2.2 hed).mono (hlensO e) (hlensO d)
  have hCpU : ∀ w, Cp w ⊆ U := fun w => (hsub w).2.1.trans (hsub w).2.2
  obtain ⟨Kcore, hcore, hcoreCover⟩ :=
    exists_section34_graph_cores_of_isPLCellOn hcp hCpU hvertex hcover
  have hcoreI (w) : IsCompact (Kcore w) ∧ Kcore w ⊆ interior (Cp w) := by
    refine ⟨(hcore w).1, ?_⟩
    rw [← (hcp w).sdiff_boundary_eq_interior]
    exact (hcore w).2.2
  obtain ⟨tubeO, htubeOpen, hcircleO, htubeCc, htubeU, htubeLF, htubeDisj,
    htubeGraph, htubeCore, htubeForeign⟩ := exists_section34_piercing_circle_neighborhoods
      hU ends Cp CpBd Cc Kcore hcp hCpU hCpCc hcover hCpLF hcoreI hnonadj
      diskO hdiskO.1 hdiskO.2.2.2.1 hdiskO.2.2.2.2 hlensO
  have exists_marked_nested_piercing_annuli :
      ∃ (Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁),
      (∀ e, IsLocallyFiniteRegularNeighborhoodOf (n := 3) (Sn e)
            (CpBd (ends e).1 ∩ CpBd (ends e).2) U ∧
          IsLocallyFiniteRegularNeighborhoodOf (n := 3) (Tn e)
            (CpBd (ends e).1 ∩ CpBd (ends e).2) U) ∧
      (∀ e, Tn e ⊆ interior (Sn e) ∧ IsTopologicalSolidTorus (Sn e) ∧
          IsTopologicalSolidTorus (Tn e)) ∧
      (∀ e, Sn e ⊆ tubeO e) ∧
      (∀ e, Aa e = CpBd (ends e).1 ∩ Tn e ∧ IsAnnulusOn (Aa e) (Ab₀ e) (Ab₁ e)) ∧
      (∀ e, Bb e ⊆ CpBd (ends e).2 ∧ IsAnnulusOn (Bb e) (Bb₀ e) (Bb₁ e)) ∧
      (∀ e, Tn e ∩ CpBd (ends e).2 ⊆ Bb e \ (Bb₀ e ∪ Bb₁ e)) ∧
      (∀ e, Bb e ⊆ interior (Sn e) ∧ Bb₀ e ∪ Bb₁ e ⊆ Sn e \ Tn e) ∧
      (∀ e, IsAnnulusOn (Bc e) (Bc₀ e) (Bc₁ e) ∧ Bc e ⊆ Bb e ∩ interior (Tn e)) ∧
      (∀ e, CpBd (ends e).1 ∩ CpBd (ends e).2 ⊆ Bc e \ (Bc₀ e ∪ Bc₁ e)) ∧
      (∀ e, Ab₀ e ⊆ interior (Cp (ends e).2) ∧ Ab₁ e ∩ Cp (ends e).2 = ∅) ∧
      (∀ e, (∃ y₀ ∈ Bb e ∩ Cp (ends e).1, ∀ z ∈ Bb e ∩ Cp (ends e).1, z ∉ Tn e →
            z ∈ connectedComponentIn (Bb e ∩ Cp (ends e).1) y₀) ∧
          ∃ y₀ ∈ Bb e \ Cp (ends e).1, ∀ z ∈ Bb e \ Cp (ends e).1, z ∉ Tn e →
            z ∈ connectedComponentIn (Bb e \ Cp (ends e).1) y₀) := by
    have hex (e) := hN.1.exists_marked_nested_piercing_annuli hU (hcircle e).1
      (hcc (ends e).1).isPolyhedralBall (hCcU (ends e).1)
      ((hcircle e).2.trans (((hends e).2.2.subset.trans inter_subset_left).trans (hsrcCc _)))
      (htubeOpen e) (hcircleO e)
      (hcp (ends e).1).isPolyhedralSphere_boundary (hcp (ends e).2).isPolyhedralSphere_boundary
      ((hcp (ends e).1).boundary_subset.trans (hCpU _))
      ((hcp (ends e).2).boundary_subset.trans (hCpU _))
      inter_subset_left inter_subset_right (hcp (ends e).1).isCompact.isClosed
      (hcp (ends e).2).isCompact.isClosed rfl (inter_comm _ _)
      (hcross e).1 (hcross e).2.1 (hcross e).2.2.1 (hcross e).2.2.2
    choose Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁
      hS hT hTS htS htT hSO hAa hBb htb hbs hbc hcirclebc hab hcompIn hcompOut using hex
    refine ⟨Sn, Tn, Aa, Ab₀, Ab₁, Bb, Bb₀, Bb₁, Bc, Bc₀, Bc₁,
      fun e => ⟨hS e, hT e⟩, fun e => ⟨hTS e, htS e, htT e⟩, hSO,
      fun e => ⟨(hAa e).1, (hAa e).2.1⟩, hBb, htb, hbs, hbc, hcirclebc, hab, ?_⟩
    intro e
    obtain ⟨y₀, hy₀⟩ := (hcompIn e).nonempty
    obtain ⟨y₁, hy₁⟩ := (hcompOut e).nonempty
    exact ⟨⟨y₀, hy₀, fun _ hz _ =>
      (hcompIn e).isPreconnected.subset_connectedComponentIn hy₀ Subset.rfl hz⟩,
      ⟨y₁, hy₁, fun _ hz _ =>
        (hcompOut e).isPreconnected.subset_connectedComponentIn hy₁ Subset.rfl hz⟩⟩
  obtain ⟨Sn, Tn, Aa, Ab₀, Ab₁, Bb, Bb₀, Bb₁, Bc, Bc₀, Bc₁,
    hreg, htorus', hSnO, haa, hbb, htb, hbs, hbc, hcirclebc, hab, hcomp⟩ :=
    exists_marked_nested_piercing_annuli
  have htorus (e) : Tn e ⊆ interior (Sn e) ∧ IsTopologicalSolidTorus (Sn e) ∧
      IsTopologicalSolidTorus (Tn e) ∧ Disjoint (Sn e) (graphSkeletonSpace 𝒦) :=
    ⟨(htorus' e).1, (htorus' e).2.1, (htorus' e).2.2,
      (htubeGraph e).mono_left (hSnO e)⟩
  have hincident (e) (w) (hw : w = (ends e).1 ∨ w = (ends e).2) : Sn e ⊆ Cc w := by
    intro x hx
    have hC := (htubeCc e (hSnO e hx)).2
    rcases hw with rfl | rfl
    · exact interior_subset hC.1
    · exact interior_subset hC.2
  have htubes (e d) (hed : e ≠ d) : Disjoint (Sn e) (Sn d) :=
    (htubeDisj hed).mono (hSnO e) (hSnO d)
  have hSnLF : LocallyFinite fun e => {x : U | (x : M₁) ∈ Sn e} :=
    htubeLF.subset (fun e _ hx => hSnO e hx)
  have hSnK (e w) : Disjoint (Sn e) (Kcore w) := (htubeCore e w).mono_left (hSnO e)
  have hSnBd (e w) (hw₀ : w ≠ (ends e).1) (hw₁ : w ≠ (ends e).2) :
      Disjoint (Sn e) (CpBd w) :=
    (htubeForeign e w hw₀ hw₁).mono (hSnO e) (hcp w).boundary_subset
  have hgen (e) : CarriesFundamentalGroupOnto (Ab₀ e) (Tn e) ∧
      CarriesFundamentalGroupOnto (Ab₁ e) (Tn e) ∧
      CarriesFundamentalGroupOnto (Ab₀ e) (Sn e) := by
    have hJ : (CpBd (ends e).1 ∩ CpBd (ends e).2).Nonempty := by
      obtain ⟨P, hP⟩ := (hcircle e).1
      obtain ⟨x, hx⟩ := hP.nonempty
      exact ⟨P.piece.map x, P.piece.bijOn.mapsTo hx⟩
    have hTgen := (hreg e).2.carriesFundamentalGroupOnto
    have hSgen := (hreg e).1.carriesFundamentalGroupOnto
    have hJA : CpBd (ends e).1 ∩ CpBd (ends e).2 ⊆ Aa e := by
      rw [(haa e).1]
      exact fun x hx => ⟨hx.1, hTgen.1 hx⟩
    have hAT : Aa e ⊆ Tn e := by
      rw [(haa e).1]
      exact inter_subset_right
    obtain ⟨hzero, hone⟩ := (haa e).2.boundaries_carry_of_core hTgen hJ hJA hAT
    exact ⟨hzero, hone, ((haa e).2.boundaries_carry_of_core hSgen hJ hJA
      (hAT.trans ((htorus e).1.trans interior_subset))).1⟩
  have exists_vertex_scales_with_sum_margins :
      ∃ μ : Section34VertexIndex 𝒦 𝒦' → ℝ,
      (∀ w, 0 < μ w) ∧
      (∀ w, ∀ x ∈ Cc w, Metric.ball (h x) (μ w) ⊆ interior (Q w)) ∧
      (∀ e, ∀ x ∈ Sn e, Metric.ball (h x) (μ (ends e).1 + μ (ends e).2) ⊆
          interior (Q (ends e).1) ∩ interior (Q (ends e).2)) ∧
      (∀ w, ∀ x ∈ CcBd w, ∀ y ∈ h '' simplexBody 𝒦' w.1, μ w < dist (h x) y) ∧
      (∀ w, ∀ x ∈ CpBd w, ∀ y ∈ h '' simplexBody 𝒦' w.1, μ w < dist (h x) y) ∧
      (∀ e, ∀ x ∈ Bb₀ e ∪ Bb₁ e, ∀ y ∈ Tn e,
          μ (ends e).1 + μ (ends e).2 < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ CpBd (ends e).1 \ (Aa e \ (Ab₀ e ∪ Ab₁ e)), ∀ y ∈ CpBd (ends e).2,
          μ (ends e).1 + μ (ends e).2 < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ CpBd (ends e).1, ∀ y ∈ CpBd (ends e).2 \ (Bb e \ (Bb₀ e ∪ Bb₁ e)),
          μ (ends e).1 + μ (ends e).2 < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ Ab₁ e, ∀ y ∈ Cp (ends e).2,
          μ (ends e).1 + μ (ends e).2 < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ Bb e, ∀ y ∈ Cc (ends e).1 \ interior (Sn e),
          μ (ends e).1 + μ (ends e).2 < dist (h x) (h y)) ∧
      (∀ e, ∀ x ∈ Bc₀ e ∪ Bc₁ e, ∀ y ∈ Sn e \ interior (Tn e),
          μ (ends e).1 + μ (ends e).2 < dist (h x) (h y)) ∧
      (∀ e, ∀ w, w = (ends e).1 ∨ w = (ends e).2 →
          ∀ x ∈ Sn e, ∀ y ∈ graphSkeletonSpace 𝒦, μ w < dist (h x) (h y)) ∧
      (∀ e w, ∀ x ∈ Sn e, ∀ y ∈ simplexBody 𝒦' w.1,
          μ (ends e).1 + μ w < dist (h x) (h y)) ∧
      (∀ e w, w ≠ (ends e).1 → w ≠ (ends e).2 → ∀ x ∈ Sn e, ∀ y ∈ CpBd w,
          μ (ends e).1 + μ w < dist (h x) (h y)) ∧
      (∀ w w', Disjoint (Cp w) (Cp w') → ∀ x ∈ Cp w, ∀ y ∈ Cp w',
          μ w + μ w' < dist (h x) (h y)) ∧
      (∀ e d, e ≠ d → ∀ x ∈ Sn e, ∀ y ∈ Sn d,
          μ (ends e).1 + μ (ends d).1 < dist (h x) (h y)) ∧
      (∀ e w, ∀ x ∈ Sn e, ∀ y ∈ Kcore w, μ (ends e).1 + μ w < dist (h x) (h y)) ∧
      (∀ w w', w ≠ w' → ∀ x ∈ Cp w', ∀ y ∈ simplexBody 𝒦' w.1, μ w' < dist (h x) (h y)) := by
    obtain ⟨cap, margin, hcap, hmargin, hball, hballSum, hccDist, hcpDist, hbbDist,
      haaDist, hbbDist', habDist, hbccDist, hbcsDist⟩ := exists_section34_local_margins
      hh hcc hcp (fun w => (hsub w).2.2) hCpCc hvertex hQ
      (fun e => (htorus e).2.1) (fun e => (htorus e).2.2.1)
      (fun e => (htorus e).1) hincident haa hbb htb hbs hbc hcirclebc hab
    have hSnCompact (e) : IsCompact (Sn e) := by
      obtain ⟨φ⟩ := (htorus e).2.1
      have : CompactSpace (Sn e) := φ.symm.compactSpace
      exact isCompact_iff_compactSpace.mpr inferInstance
    have hSnU (e) : Sn e ⊆ U :=
      (hincident e _ (Or.inl rfl)).trans (hsub _).2.2
    obtain ⟨μ, hμ, hμcap, hμmargin, hgraph, hmarks, hforeign, hcells, htubedist,
      hcoredist, hvertexdist⟩ := exists_section34_separation_margins hh
      (fun e => (hends e).2.1) hcp hCpU hCpLF hSnCompact hSnU hSnLF hcore hcoreCover
      hSnK hSnBd htubes hvdisj cap hcap margin hmargin
    refine ⟨μ, hμ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hgraph, hmarks,
      hforeign, hcells, htubedist, hcoredist, hvertexdist⟩
    · intro w x hx
      exact (Metric.ball_subset_ball (hμcap w).le).trans (hball w x hx)
    · intro e x hx
      exact (Metric.ball_subset_ball (hμmargin e).le).trans (hballSum e x hx)
    · intro w x hx y hy
      exact (hμcap w).trans (hccDist w x hx y hy)
    · intro w x hx y hy
      exact (hμcap w).trans (hcpDist w x hx y hy)
    · intro e x hx y hy
      exact (hμmargin e).trans (hbbDist e x hx y hy)
    · intro e x hx y hy
      exact (hμmargin e).trans (haaDist e x hx y hy)
    · intro e x hx y hy
      exact (hμmargin e).trans (hbbDist' e x hx y hy)
    · intro e x hx y hy
      exact (hμmargin e).trans (habDist e x hx y hy)
    · intro e x hx y hy
      exact (hμmargin e).trans (hbccDist e x hx y hy)
    · intro e x hx y hy
      exact (hμmargin e).trans (hbcsDist e x hx y hy)
  obtain ⟨μ, hμ, hball, hballSum, hccDist, hcpDist, hbbDist, haaDist, hbbDist', habDist,
    hbccDist, hbcsDist, hgraphDist, hmarkDist, hforeignDist, hdisjDist, hsnDist,
    hcoreDist, hvertexDist⟩ := exists_vertex_scales_with_sum_margins
  obtain ⟨δ, hδ, hδμ, hstable⟩ := exists_core_stability_scales_lt hh hcp hCpU
    (fun w => (hcore w).1) (fun w => (hcore w).2.2) hμ
  obtain ⟨ε, hε, hεδ, hoverlap⟩ :=
    exists_section34_overlap_isolation_scales hU hh (fun e => (hends e).2.1)
      (fun w => (hcp w).isCompact) hCpU hCpLF hlens δ hδ
  have hεμ (w : Section34VertexIndex 𝒦 𝒦') : ε w ≤ μ w :=
    (hεδ w).le.trans (hδμ w).le
  have hsum (v w : Section34VertexIndex 𝒦 𝒦') : ε v + ε w ≤ μ v + μ w :=
    add_le_add (hεμ v) (hεμ w)
  refine ⟨Cp, CpBd, Cc, CcBd, Kcore, ends, Sn, Tn, Aa, Ab₀, Ab₁, Bb, Bb₀, Bb₁,
    Bc, Bc₀, Bc₁, ε, hε, hcc, hsub, hchart, hcp, hvertex, hQ, hLF, hends, hcircle,
    hreg, htorus, hincident, htubes, haa, hbb, htb, hbs, hbc, hcirclebc, hab, hcomp, hgen,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcore, hcoreCover,
    ?_, ?_, ?_, hnonadj, hoverlap⟩
  · intro w x hx
    exact (Metric.ball_subset_ball (hεμ w)).trans (hball w x hx)
  · intro e x hx
    exact (Metric.ball_subset_ball (hsum _ _)).trans (hballSum e x hx)
  · intro w x hx y hy
    exact (hεμ w).trans_lt (hccDist w x hx y hy)
  · intro w x hx y hy
    exact (hεμ w).trans_lt (hcpDist w x hx y hy)
  · intro e x hx y hy
    exact (hsum _ _).trans_lt (hbbDist e x hx y hy)
  · intro e x hx y hy
    exact (hsum _ _).trans_lt (haaDist e x hx y hy)
  · intro e x hx y hy
    exact (hsum _ _).trans_lt (hbbDist' e x hx y hy)
  · intro e x hx y hy
    exact (hsum _ _).trans_lt (habDist e x hx y hy)
  · intro e x hx y hy
    exact (hsum _ _).trans_lt (hbccDist e x hx y hy)
  · intro e x hx y hy
    exact (hsum _ _).trans_lt (hbcsDist e x hx y hy)
  · intro e w hw x hx y hy
    exact (hεμ w).trans_lt (hgraphDist e w hw x hx y hy)
  · intro e w x hx y hy
    exact (hsum _ _).trans_lt (hmarkDist e w x hx y hy)
  · intro e w hwa hwb x hx y hy
    exact (hsum _ _).trans_lt (hforeignDist e w hwa hwb x hx y hy)
  · intro w w' hw x hx y hy
    exact (hsum _ _).trans_lt (hdisjDist w w' hw x hx y hy)
  · intro e d hed x hx y hy
    exact (hsum _ _).trans_lt (hsnDist e d hed x hx y hy)
  · intro w F hF hclose
    exact hstable w F hF fun x hx => (hclose x hx).trans (hεδ w)
  · intro e w x hx y hy
    exact (hsum _ _).trans_lt (hcoreDist e w x hx y hy)
  · intro w w' hww x hx y hy
    exact (hεμ w').trans_lt (hvertexDist w w' hww x hx y hy)

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
