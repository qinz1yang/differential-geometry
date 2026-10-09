/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCompressionCarrier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompressionInside

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {C V : Set E3} {K K' : Geometry.SimplicialComplex ℝ E3}
  {src srcBd : Section34CompactLabelOf K K' → Set E3} {h f₁ : E3 → E3} {ε : ℝ}
  {H : Finset E3 → Set E3}

theorem exists_compactCompression_of_subset
    (hcut : Section34CompactCutFrame C K K' src srcBd)
    (hgraph : Section34CompactGraphFrame V h ε K K' src H f₁)
    {fbl fblBd : Section34CompactSimplexIndex K 3 → Set E3}
    (hinv : Section34CompactFaceBallInvariants K K' h H
      (section34CompactVertexBallImage src f₁) (section34CompactSplitDiskImage srcBd f₁)
      fbl fblBd) (s : Section34CompactSimplexIndex K 3)
    {w : Section34CompactVertexIndex K K'} {Dj Jd : Set E3}
    (hDcell : IsPLCellOn 2 Dj Jd) (hDw : Dj ⊆ section34CompactVertexBallImage srcBd f₁ w)
    (hDJ : Dj ∩ fblBd s = Jd)
    (hDE : ∀ e, Disjoint Dj (section34CompactSplitDiskImage src f₁ e)) (hDs : Dj ⊆ fbl s) :
    ∃ fbl' fblBd' : Section34CompactSimplexIndex K 3 → Set E3,
      Section34CompactFaceBallInvariants K K' h H (section34CompactVertexBallImage src f₁)
        (section34CompactSplitDiskImage srcBd f₁) fbl' fblBd' ∧
      (∀ s', s' ≠ s → fbl' s' = fbl s' ∧ fblBd' s' = fblBd s') ∧
      section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd' s + 1 ≤
        section34CompactTraceCount (section34CompactVertexBallImage src f₁) fblBd s ∧
      section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd' s ≤
        section34CompactCrossingCount (section34CompactSplitDiskImage srcBd f₁) fblBd s := by
  classical
  obtain ⟨hfcell, hfrim, -, -, hf5, -, hf7, -, -, -, -⟩ := id hinv
  obtain ⟨-, hf₁, -, -, -, -, -, hrimT, hnest, -⟩ := id hgraph
  let _ : Finite (Section34CompactEdgeIndex K K') :=
    finite_section34CompactGraphIndex hcut.2.2.1 _ 2
  have hVcell := hcut.isPLCellOn_vertexBallImage hf₁
  have hEcell := hcut.isPLCellOn_splitDiskImage hf₁
  obtain ⟨O₀, hO₀, hfO₀, hSgO₀, -⟩ := hinv.exists_isOpen_frontier_eq hcut.2.2.1
    (fun v => (hVcell v).isCompact.isClosed) s
  obtain ⟨Oo, hOo, hDO, hSgOo, -, -⟩ := hcut.exists_isOpen_compression_disk hf₁ hDw hDE
  set T := section34CompactFaceTorus (section34CompactVertexBallImage src f₁) s
  set Sg := frontier (⋃ v, section34CompactVertexBallImage src f₁ v)
  set Θ := frontier T
  have hSgT : ∀ x ∈ O₀, (x ∈ Sg ↔ x ∈ Θ) := by
    intro x hx
    have he := Iff.of_eq (congrArg (fun A => x ∈ A) hSgO₀)
    simpa only [mem_inter_iff, hx, and_true] using he
  have hVfr := (hVcell w).boundary_eq_frontier
  have hDV : Dj ⊆ frontier (section34CompactVertexBallImage src f₁ w) := hDw.trans hVfr.subset
  have hDjSg : Dj ⊆ Sg := by
    intro x hx
    have hmem : x ∈ frontier (section34CompactVertexBallImage src f₁ w) ∩ Oo := ⟨hDV hx, hDO hx⟩
    rw [← hSgOo] at hmem
    exact hmem.1
  have hDjT : Dj ⊆ Θ := fun x hx => (hSgT x (hfO₀ (hDs hx))).mp (hDjSg hx)
  have hOΘ : (Oo ∩ O₀) ∩ Θ = (Oo ∩ O₀) ∩
      frontier (section34CompactVertexBallImage src f₁ w) := by
    ext x
    by_cases hx : x ∈ Oo ∩ O₀
    · have hv : x ∈ Sg ↔ x ∈ frontier (section34CompactVertexBallImage src f₁ w) := by
        have he := congrArg (fun A => x ∈ A) hSgOo
        simpa only [mem_inter_iff, hx.1, and_true] using Iff.of_eq he
      simp only [mem_inter_iff, hx, true_and]
      exact (hSgT x hx.2).symm.trans hv
    · simp only [mem_inter_iff, hx, false_and]
  have hPb := (hfcell s).isPLBall_three
  have hPfr := (hfcell s).boundary_eq_frontier
  have hfbs := (hfcell s).boundary_subset
  have hcross : ∀ x ∈ frontier (fbl s) ∩ Θ,
      HasPLCrossingAt (frontier (fbl s)) Θ x := by
    rintro x ⟨hxP, hxΘ⟩
    have hxb : x ∈ fblBd s := hPfr.symm ▸ hxP
    have hxO := hfO₀ (hfbs hxb)
    have hcr := hf5 s x ⟨hxb, (hSgT x hxO).mpr hxΘ⟩
    rw [hPfr] at hcr
    refine hcr.congr (Filter.Eventually.of_forall fun _ => Iff.rfl) ?_
    filter_upwards [hO₀.mem_nhds hxO] with z hz
    exact hSgT z hz
  obtain ⟨q, hq, hqJ⟩ := hDcell.exists_isPLHomeomorphOn_stdSimplex
  have hJdD := hDcell.boundary_subset
  have hJdb : Jd ⊆ fblBd s := hDJ.symm.subset.trans inter_subset_right
  have htrace : Dj ∩ frontier (fbl s) = q '' stdSimplexBoundary 2 := by
    rw [← hPfr, hDJ, hqJ]
  have hEc : IsClosed (⋃ e, section34CompactSplitDiskImage src f₁ e) :=
    isClosed_iUnion_of_finite fun e => (hEcell e).isCompact.isClosed
  have hDEc : Disjoint Dj (⋃ e, section34CompactSplitDiskImage src f₁ e) := by
    refine disjoint_left.mpr fun x hx hxe => ?_
    obtain ⟨e, he⟩ := mem_iUnion.mp hxe
    exact disjoint_left.mp (hDE e) hx he
  have hKD : Disjoint (h '' section34CompactSimplexRim s.1) Dj :=
    disjoint_left.mpr fun x hx hxD => (hDjT hxD).2 (hrimT s hx)
  obtain ⟨G, Oc, hG, hGP, hrimG, hGD, hOc, hfrO, hk2, hk4, hk3⟩ :=
    hPb.exists_compression_trace hq hDs htrace (hVcell w).isPLBall_three.isPLSphere_frontier
      hDV (hOo.inter hO₀) (fun x hx => ⟨hDO hx, hfO₀ (hDs hx)⟩) hOΘ
      (fun x hx => hcross x ⟨hPfr ▸ hJdb (hqJ.symm ▸ hx), hDjT (hJdD (hqJ.symm ▸ hx))⟩)
      hEc hDEc (hgraph.isCompact_image_simplexRim s)
      (hgraph.isConnected_image_simplexRim s).isPreconnected (hfrim s) hKD
  have hGc := hG.isPolyhedron.isClosed
  have hfrGG := hGc.frontier_subset
  obtain ⟨S₁, S₂, -, -, hTsolid, -⟩ := hnest s
  have hTcl := hTsolid.isPolyhedron.isClosed
  have hΘtor := hTsolid.isPLTorus_frontier
  have hTreg : ∀ x ∈ Θ, x ∈ closure (interior T) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hTcl.frontier_subset hx)
    have hv : section34CompactVertexBallImage src f₁ a.1.2 ⊆ T :=
      fun y hy => mem_iUnion₂.mpr ⟨a, ha, hy⟩
    have hcl := (hVcell a.1.2).isPLBall_three.closure_interior_of_finrank (by simp)
    exact closure_mono (interior_mono hv) (hcl.symm ▸ hxa)
  obtain ⟨ι, hιfin, Cs, hCs, hCsd, hCseq⟩ := exists_iUnion_isPLSphere_one_of_forall_lineChart
    (hPb.isPolyhedron.frontier.inter hΘtor.1) hcross fun x hx =>
      (hcross x hx).exists_lineChart hx.1
        (hPb.isPLSphere_frontier.exists_isOpen_inter_homeomorph_of_two hx.1) hTcl (hTreg x hx.2)
  have hZGO : frontier (fbl s) ∩ Θ ∩ G = frontier (fbl s) ∩ Θ ∩ Oc := by
    rw [← hk3]
    ext x
    constructor
    · rintro ⟨hx, hxΘ⟩
      have h1 : x ∈ frontier G ∩ Oc := ⟨hx, hk2 ⟨hx, hxΘ⟩⟩
      rw [hfrO] at h1
      exact ⟨⟨h1.1, hxΘ⟩, h1.2⟩
    · rintro ⟨⟨hx, hxΘ⟩, hxO⟩
      have h1 : x ∈ frontier (fbl s) ∩ Oc := ⟨hx, hxO⟩
      rw [← hfrO] at h1
      exact ⟨h1.1, hxΘ⟩
  have hWS : CarriesFirstHomologyOnto (G ∩ Θ) T := by
    have hFint : CarriesFirstHomologyOnto (G ∩ interior T) T :=
      (hgraph.carriesFirstHomologyOnto s).mono
        (fun x hx => ⟨interior_subset (hrimG hx), hrimT s hx⟩)
        (inter_subset_right.trans interior_subset)
    obtain ⟨A, B, hAfin, hBA, hAsp, hBsp⟩ :=
      exists_simplicialComplex_subcomplex_of_isPolyhedron
        (hG.isPolyhedron.inter hTsolid.isPolyhedron) (hG.isPolyhedron.inter hΘtor.1)
        (inter_subset_inter_right _ hTcl.frontier_subset)
    let _ : Finite A.faces := hAfin.to_subtype
    exact hFint.inter_frontier_of_chart hGc hTcl
      hG.isPLCellOn_frontier.subsingleton_integralSingularHomology_one
      (c := chartAt E3 (0 : E3)) (by rw [chartAt_self_eq]; exact subset_univ _) A B hBA
      (by rw [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, image_id]; exact hAsp)
      (by rw [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, image_id]; exact hBsp)
  have hfrZ : ∀ x ∈ G ∩ Θ, x ∉ interior G → x ∈ frontier (fbl s) ∩ Θ := by
    intro x hx hxi
    have hxf : x ∈ frontier G ∩ Θ := ⟨⟨subset_closure hx.1, hxi⟩, hx.2⟩
    rw [hk3] at hxf
    exact hxf.1
  have hZS : CarriesFirstHomologyOnto (id '' (frontier (fbl s) ∩ Θ)) T := by
    rw [image_id, ← hPfr]
    exact hf7 s
  have h7 : CarriesIntegralFirstHomologyOnto (frontier G ∩ Θ) T := by
    have hc := hΘtor.carriesFirstHomologyOnto_image_inter_of_isClopen hCs hCsd hCseq
      inter_subset_right hGc hOc hZGO hfrZ continuousOn_id (fun _ _ _ _ he => he)
      (by rw [image_id]; exact hTcl.frontier_subset) hZS (by simpa only [image_id] using hWS)
    change CarriesFirstHomologyOnto (frontier G ∩ Θ) T
    rw [hk3]
    simpa only [image_id] using hc
  obtain ⟨y₀, hy₀⟩ : Jd.Nonempty := by
    rw [hqJ]
    exact (nonempty_stdSimplexBoundary_of_pos (by decide : 0 < 2)).image q
  have hy₀G : y₀ ∉ G := fun hy => disjoint_left.mp hGD hy (hJdD hy₀)
  have hr : ∀ t : Section34CompactSimplexIndex K 4, Section34Incident s.1 t.1 →
      ∃ (r : E3 → E3) (Y B : Set E3), IsCompact Y ∧ Bornology.IsBounded B ∧
        frontier Y ⊆ section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t ∧
        ContinuousOn r ((section34CompactTetraObstacle
          (section34CompactVertexBallImage src f₁) fbl t)ᶜ \ Y) ∧
        MapsTo r ((section34CompactTetraObstacle (section34CompactVertexBallImage src f₁)
          fbl t)ᶜ \ Y)
          (section34CompactTetraObstacle (section34CompactVertexBallImage src f₁) fbl t ∪ ∅)ᶜ ∧
        (∀ x ∉ B, r x = x) ∧
        ∀ v : Section34CompactVertexIndex K K', ¬ Section34Incident v.1 t.1 →
          ∀ y ∈ h '' (v.1 : Set E3), r y = y := by
    intro t _
    refine ⟨id, ∅, ∅, isCompact_empty, Bornology.isBounded_empty, by simp, continuousOn_id, ?_,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    intro x hx
    simpa only [union_empty, id_eq] using hx.1
  exact exists_compactCompression_of_ball hinv s hfO₀ hSgO₀ hG (hGP.trans hfO₀) hrimG
    (hGP.trans subset_union_left) (fun _ _ => by simp)
    (fun _ _ => by simp) (fun _ _ => empty_subset _) hr hOc
    (by rw [hPfr]; exact hfrO) hk2
    (fun e x hx => hk4 ⟨hx.1, mem_iUnion.mpr ⟨e, (hEcell e).boundary_subset hx.2⟩⟩)
    (by rw [hPfr]; exact hk3) hGc ⟨hJdb hy₀, hDjSg (hJdD hy₀)⟩ hy₀G h7

end DifferentialGeometry.Topology.PiecewiseLinear
