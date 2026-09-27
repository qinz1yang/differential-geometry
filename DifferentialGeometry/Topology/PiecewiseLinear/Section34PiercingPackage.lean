/-
Copyright (c) 2026 Bennett Chow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bennett Chow
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34RelativeVertexCrossings
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingAnnularCrossings
import DifferentialGeometry.Topology.PiecewiseLinear.CrossingTracePolyhedron
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexChartScales
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingAuxiliaryScales
import DifferentialGeometry.Topology.PiecewiseLinear.Section34VertexApproximation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingConditionsOfCrossings
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingCircles
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingNonempty

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

theorem exists_section34PiercingPackage [T2Space M₁] [SecondCountableTopology M₁]
    [SecondCountableTopology M₂] [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
    (h341 : Moise341) (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (hN : IsLocallyFiniteRegularNeighborhoodOf (n := 3) (section34CutNeighborhood src)
      (graphSkeletonSpace 𝒦) U)
    (hQsub : ∀ w, Q w ⊆ h '' U)
    (hQlfU : LocallyFinite fun w => {y : h '' U | (y : M₂) ∈ Q w})
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε) :
    ∃ (Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂) (cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂)
      (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂),
      Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁
          Sp Tp cnt Pg G' ∧
        ∀ w, ∀ x ∈ Cc w, dist (G' w x) (h x) < ε w := by
  let _ := (inferInstance : SecondCountableTopology M₁)
  let _ := (inferInstance : SecondCountableTopology M₂)
  let _ := (inferInstance : FiniteDimensional ℝ Ea)
  let _ := hU
  let _ := hN
  let _ := hQsub
  obtain ⟨δs, hδs, hδsε, hsides⟩ := exists_auxiliary_scales_preserving_piercing_sides hh hprep
  obtain ⟨c, δc, hc, hδc, -, hcharts⟩ :=
    exists_section34_vertex_chart_stability_scales hh hprep
  obtain ⟨δr, hδr, -, hright⟩ :=
    exists_section34_second_trace_interior_stability_scales hh hprep
  let δ (w : Section34VertexIndex 𝒦 𝒦') := min (δs w) (min (δc w) (δr w))
  have hδ (w : Section34VertexIndex 𝒦 𝒦') : 0 < δ w :=
    lt_min (hδs w) (lt_min (hδc w) (hδr w))
  have hδε (w : Section34VertexIndex 𝒦 𝒦') : δ w < ε w :=
    (min_le_left _ _).trans_lt (hδsε w)
  obtain ⟨-, hcc, hsubs, hchart, -⟩ := id hprep
  obtain ⟨G₀, hG₀, hG₀dist⟩ := h341.exists_chart_local_cell_approximations hh Cc CcBd hcc
    (fun w => (hsubs w).2.2) hchart (fun w => δ w / 3)
    (fun w => div_pos (hδ w) (by norm_num))
  let A (F : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e : Section34EdgeIndex 𝒦 𝒦') :=
    F (ends e).1 '' Aa e
  let B (F : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e : Section34EdgeIndex 𝒦 𝒦') :=
    F (ends e).2 '' Bb e
  have hG₀δ : ∀ w, ∀ x ∈ Cc w, dist (G₀ w x) (h x) < δ w := by
    intro w x hx
    linarith [hG₀dist w x hx, hδ w]
  have hG₀chart := hcharts G₀ (fun w x hx =>
    (hG₀δ w x hx).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨G, hG, hGG₀, -, hboundaryCross⟩ := exists_section34_relative_vertex_crossings hprep
    hG₀ (fun w x hx => (hG₀δ w x hx).trans (hδε w)) hc hG₀chart
    (fun w => div_pos (hδ w) (show (0 : ℝ) < 3 by norm_num))
  have hGδ : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w := by
    intro w x hx
    have ht := dist_triangle (G w x) (G₀ w x) (h x)
    linarith [hGG₀ w x, hG₀dist w x hx, hδ w]
  have hGdist : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w :=
    fun w x hx => (hGδ w x hx).trans (hδε w)
  obtain ⟨htraceInside, hAb₀Inside, hBbInside, hcomponentInside, hcomponentOutside⟩ :=
    hsides G hG (fun w x hx => (hGδ w x hx).trans_le (min_le_left _ _))
  have hGchart := hcharts G (fun w x hx =>
    (hGδ w x hx).trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have htraceRight := hright G hG (fun w x hx =>
    (hGδ w x hx).trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have htraceCharts := section34_piercing_annular_crossings hprep hG htraceInside htraceRight
    (fun e => c (ends e).1) (fun e y hy _ => hboundaryCross e y hy)
  obtain ⟨-, -, -, -, hcp, -, -, -, -, -, -, -, -, -, haa, hbb, -⟩ := id hprep
  have hAaCc (e : Section34EdgeIndex 𝒦 𝒦') : Aa e ⊆ Cc (ends e).1 := by
    rw [(haa e).1]
    exact inter_subset_left.trans ((hcp _).boundary_subset.trans (hsubs _).2.1)
  have hGp : ∀ w, IsPLHomeomorphInto 3 (G w) (Cp w) := fun w =>
    (hG w).mono_of_isPLCellOn (hcp w) (hsubs w).2.1
  have hne := section34_piercing_trace_nonempty hprep hGp hGdist hAb₀Inside
  have hfamily (e : Section34EdgeIndex 𝒦 𝒦') :
      ∃ (cnt : ℕ) (Pg : ℕ → Set M₂), 0 < cnt ∧ A G e ∩ B G e = ⋃ i < cnt, Pg i ∧
        (∀ i < cnt, IsPolyhedralSphere (n := 3) 1 (Pg i) ∧ Pg i ⊆ A G e ∩ B G e) ∧
        (∀ i < cnt, ∀ j < cnt, i ≠ j → Disjoint (Pg i) (Pg j)) ∧
        ∀ y ∈ A G e ∩ B G e, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
          HasPLCrossingAt (c '' (A G e ∩ c.source)) (c '' (B G e ∩ c.source)) (c y) := by
    have hcross := fun x hx => (htraceCharts e x hx).1
    have hline := fun x hx => (htraceCharts e x hx).2
    have hsource : A G e ∩ B G e ⊆ (c (ends e).1).source :=
      inter_subset_left.trans ((image_mono (hAaCc e)).trans (hGchart _))
    have hAc : IsCompact (A G e) := (haa e).2.isCompact.image_of_continuousOn
      ((hG _).continuousOn.mono (hAaCc e))
    have hBc : IsCompact (B G e) := (hbb e).2.isCompact.image_of_continuousOn
      ((hG _).continuousOn.mono ((hbb e).1.trans
        ((hcp _).boundary_subset.trans (hsubs _).2.1)))
    have hpoly := isPolyhedron_chart_inter_of_isCompact_of_hasPLCrossingAt
      (c (ends e).1) (hAc.inter hBc) hsource hcross
    exact exists_positive_finite_piercing_circle_family (c (ends e).1) (hc _) hsource
      hpoly hcross hline (hne e)
  choose cnt Pg hcnt hcover hcircles hdisj hcross using hfamily
  let Sp (e : Section34EdgeIndex 𝒦 𝒦') := G (ends e).1 '' Sn e
  let Tp (e : Section34EdgeIndex 𝒦 𝒦') := G (ends e).1 '' Tn e
  refine ⟨Sp, Tp, cnt, Pg, G, ?_, hGdist⟩
  exact piercing_conditions_of_crossings_and_margins hframe hQlfU hprep hG hGdist
    (fun _ => ⟨rfl, rfl⟩) htraceInside hAb₀Inside hBbInside hcomponentInside hcomponentOutside
    (fun e => ⟨hcnt e, hcover e⟩) hcircles hdisj hcross

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
