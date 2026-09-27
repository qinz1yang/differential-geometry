/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RelativeVertexSigns
import DifferentialGeometry.Topology.PiecewiseLinear.Section34BoundaryDiskFamilies
import DifferentialGeometry.Topology.PiecewiseLinear.CellPairRelativeOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.CellPairBoundaryOrientation
import DifferentialGeometry.Topology.PiecewiseLinear.CircleOrientationParity

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {G R : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ E3}
  {Sd : Section34SimplexIndex 𝒦 3 → Set E3}

theorem exists_section34_relative_edge_character
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends
      Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hsep : ∀ w w', w ≠ w' →
      Disjoint (h '' simplexBody 𝒦' w.1) (G w' '' Cp w'))
    (hDvsub : ∀ w, Dv w ⊆ G w '' Cp w)
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDmeet : ∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e)
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦))
    (hR : ∀ w, IsPLHomeomorphInto 3 (R w) (src (.vertexBall w)))
    (hRim : ∀ w, R w '' src (.vertexBall w) = Dv w)
    (hRD : ∀ w e, (w = (ends e).1 ∨ w = (ends e).2) →
      R w '' src (.splitDisk e) = Dd e) :
    ∃ (σ : Section34VertexIndex 𝒦 𝒦' → ZMod 2)
      (s : Section34EdgeIndex 𝒦 𝒦' → Section34SimplexIndex 𝒦 3)
      (K : Section34EdgeIndex 𝒦 𝒦' → M₂ → M₂), ∀ e,
      ct (s e) ∈ (plGroupoid 3).maximalAtlas M₂ ∧
      Q (ends e).1 ∪ Q (ends e).2 ⊆ (ct (s e)).source ∧
      IsPLHomeomorphInto 3 (K e) (Dv (ends e).1 ∪ Dv (ends e).2) ∧
      K e '' (Dv (ends e).1 ∪ Dv (ends e).2) = Dv (ends e).1 ∪ Dv (ends e).2 ∧
      K e '' Dv (ends e).1 = Dv (ends e).1 ∧ K e '' Dv (ends e).2 = Dv (ends e).2 ∧
      EqOn (K e ∘ R (ends e).2) (R (ends e).1) (src (.splitDisk e)) ∧
      circleOrientationParity (ct (s e) '' DdBd e)
        (ct (s e) ∘ K e ∘ (ct (s e)).symm) = σ (ends e).1 + σ (ends e).2 := by
  obtain ⟨H, F, σ, hHs, hFs, -, -, hH, hF, hsign⟩ :=
    exists_section34_relative_vertex_signs hU hh hframe htor hprep hsep hDvsub
      hDv hDvQ hQlf hDnbhd hR hRim
  obtain ⟨-, -, -, hcell, -, -, -, -, hcover, -⟩ := id hframe
  obtain ⟨-, -, -, -, -, -, -, -, hends, -⟩ := id hprep
  have hcharts (e : Section34EdgeIndex 𝒦 𝒦') :
      ∃ s : Section34SimplexIndex 𝒦 3, ct s ∈ (plGroupoid 3).maximalAtlas M₂ ∧
        Q (ends e).1 ∪ Q (ends e).2 ⊆ (ct s).source := by
    obtain ⟨s, -, -, -, hc, hcs⟩ :=
      exists_section34Edge_common_chart hframe htor (fun e => (hends e).2.1) e
    exact ⟨s, hc, hcs⟩
  choose s hct hcs using hcharts
  have hsrcU (w : Section34VertexIndex 𝒦 𝒦') : src (.vertexBall w) ⊆ U :=
    (subset_iUnion src (.vertexBall w)).trans hcover.subset
  have hhcont : ContinuousOn h U := continuousOn_iff_continuous_domRestrict.mpr hh.continuous
  have hhinj : InjOn h U := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hh.injective (show U.domRestrict h ⟨x, hx⟩ =
      U.domRestrict h ⟨y, hy⟩ from hxy))
  have hpoint (e : Section34EdgeIndex 𝒦 𝒦') :
      ∃ K : M₂ → M₂,
        IsPLHomeomorphInto 3 K (Dv (ends e).1 ∪ Dv (ends e).2) ∧
        K '' (Dv (ends e).1 ∪ Dv (ends e).2) = Dv (ends e).1 ∪ Dv (ends e).2 ∧
        K '' Dv (ends e).1 = Dv (ends e).1 ∧ K '' Dv (ends e).2 = Dv (ends e).2 ∧
        EqOn (K ∘ R (ends e).2) (R (ends e).1) (src (.splitDisk e)) ∧
        circleOrientationParity (ct (s e) '' DdBd e)
          (ct (s e) ∘ K ∘ (ct (s e)).symm) = σ (ends e).1 + σ (ends e).2 := by
    have hsourceU := union_subset (hsrcU (ends e).1) (hsrcU (ends e).2)
    have hDP := section34_splitDisk_subset_vertex_boundary hframe
      (fun e => (hends e).2.2) (ends e).1 e (Or.inl rfl)
    have hDQ := section34_splitDisk_subset_vertex_boundary hframe
      (fun e => (hends e).2.2) (ends e).2 e (Or.inr rfl)
    have hPh : h '' src (.vertexBall (ends e).1) ⊆ (ct (s e)).source :=
      (section34_image_vertexBall_subset_Q hprep _).trans (subset_union_left.trans (hcs e))
    have hQh : h '' src (.vertexBall (ends e).2) ⊆ (ct (s e)).source :=
      (section34_image_vertexBall_subset_Q hprep _).trans (subset_union_right.trans (hcs e))
    have hPc := (hDvQ (ends e).1).trans (subset_union_left.trans (hcs e))
    have hQc := (hDvQ (ends e).2).trans (subset_union_right.trans (hcs e))
    have hhc : h '' (src (.vertexBall (ends e).1) ∪ src (.vertexBall (ends e).2)) ⊆
        (ct (s e)).source := by rw [image_union]; exact union_subset hPh hQh
    obtain ⟨K, L, hK, hKim, hKP, hKQ, hKgf, hLs, hLt, hL, hχ⟩ :=
      exists_comparison_map_with_orientation_of_cell_pair
        (hcell (.vertexBall (ends e).1)) (hcell (.vertexBall (ends e).2))
        (hDv (ends e).1) (hDv (ends e).2) (hcell (.splitDisk e))
        (hends e).2.2.symm (hDmeet e) hDP hDQ
        ((hDdBd e).trans inter_subset_left) ((hDdBd e).trans inter_subset_right)
        (hR (ends e).1) (hRim (ends e).1) (hR (ends e).2) (hRim (ends e).2)
        (hRD (ends e).1 e (Or.inl rfl)) (hRD (ends e).2 e (Or.inr rfl))
        (hhcont.mono hsourceU) (hhinj.mono hsourceU)
        (H (ends e).1) (F (ends e).1) (H (ends e).2) (F (ends e).2)
        (hHs _) (hFs _) (hHs _) (hFs _) (hH _) (hF _) (hH _) (hF _)
        (ct (s e)) hhc (union_subset hPc hQc)
        (hsign _ _ (subset_union_left.trans (hcs e)))
        (hsign _ _ (subset_union_right.trans (hcs e)))
    obtain ⟨y, hy⟩ := (hDv (ends e).1).isConnected_interior.nonempty
    have hyO : y ∈ interior (Dv (ends e).1 ∪ Dv (ends e).2) :=
      interior_mono subset_union_left hy
    have hyL : y ∈ L.source := hLs ▸ hyO
    have hyc : y ∈ (ct (s e)).source := hPc (interior_subset hy)
    have hLyc : L y ∈ (ct (s e)).source :=
      union_subset hPc hQc (interior_subset (hLt ▸ L.map_source hyL))
    have hcircle := isPLCirclePositive_chart_iff_chartOrientationParity_eq_zero_of_cell_pair
      (hDv (ends e).1) (hDv (ends e).2) (hDd e) (hDmeet e)
      ((hDdBd e).trans inter_subset_left) ((hDdBd e).trans inter_subset_right)
      hK hKim hKP hKQ (hct e) hPc hQc L hLs hL hyL hyc hLyc
    refine ⟨K, hK, hKim, hKP, hKQ, hKgf, ?_⟩
    apply circleOrientationParity_eq_of_positive_iff
    exact hcircle.trans (by rw [hχ y hyL hyc hLyc])
  choose K hK hKim hKP hKQ hKgf hχ using hpoint
  exact ⟨σ, s, K, fun e => ⟨hct e, hcs e, hK e, hKim e, hKP e, hKQ e, hKgf e, hχ e⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
