import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorCrossingCellChain
import DifferentialGeometry.Topology.PiecewiseLinear.Section34InteriorCrossingCircleSidePages
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingChainDiagram

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem inter_eq_on_subset {E : Type*} {C N A B : Set E}
    (hCN : C ⊆ N) (hN : N ∩ A = N ∩ B) : C ∩ A = C ∩ B := by
  have h := congrArg (fun S => C ∩ S) hN
  rwa [← inter_assoc, inter_eq_left.mpr hCN, ← inter_assoc, inter_eq_left.mpr hCN] at h

open Classical in
theorem exists_interior_crossing_circle_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K K₀ K₁ : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] [Finite K₀.faces] [Finite K₁.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hdim : Module.finrank ℝ E = 3)
    (hK₀ : IsCombinatorialManifoldWithBoundary 2 K₀)
    (hK₁ : IsCombinatorialManifoldWithBoundary 2 K₁)
    (hor₀ : IsOrientable 2 K₀) (hor₁ : IsOrientable 2 K₁)
    {X Y J U : Set E} (hX : IsClosed X) (hY : IsClosed Y)
    (hregX : closure (interior X) = X) (hregY : closure (interior Y) = Y)
    (hfrontX : U ∩ K₀.space = U ∩ frontier X)
    (hfrontY : U ∩ K₁.space = U ∩ frontier Y)
    (hJ : IsPLSphere 1 J) (hJ₀ : J ⊆ K₀.space) (hJ₁ : J ⊆ K₁.space)
    (hBd₀ : Disjoint J (boundaryComplex 2 K₀).space)
    (hBd₁ : Disjoint J (boundaryComplex 2 K₁).space)
    (hJK : J ⊆ interior K.space) (hU : IsOpen U) (hJU : J ⊆ U)
    (htrace : (K₀.space ∩ K₁.space) ∩ U ⊆ J)
    (hcross : ∀ x ∈ J, HasPLCrossingAt K₀.space K₁.space x) :
    ∃ (R : Geometry.SimplicialComplex ℝ E) (f : (ℝ × ℝ) × ℝ → E),
      IsSubdivision R K ∧ R.faces.Finite ∧
      (PiecewiseLinear.restrict R J).space = J ∧
      let C := (derivedNeighborhood R (PiecewiseLinear.restrict R J)).space
      IsCylindricalDiagram f spliceSquare C ∧
      (∀ x ∈ spliceSquare, f (x, 0) = f (x, 1)) ∧
      f '' section34MarkedAxis = J ∧
      f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2) = C ∩ frontier X ∧
      f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3) = C ∩ frontier Y ∧
      (∀ i, f '' section34MarkedRibbon i = C ∩
        ![frontier X ∩ Y, frontier Y ∩ X, frontier X \ interior Y, frontier Y \ interior X] i) ∧
      C ⊆ U ∧ J ⊆ interior C := by
  obtain ⟨N, W₀, W₁, P, hN, hJN, hNU, -, -, -, -, -, -, -, hNW₀, hNW₁,
      -, -, -, -, -, hP₀, hP₂, hP₁, hP₃, -⟩ :=
    exists_interior_crossing_circle_side_pages K₀ K₁ hK₀ hK₁ hor₀ hor₁ hX hY
      hregX hregY hfrontX hfrontY hJ hJ₀ hJ₁ hBd₀ hBd₁ hU hJU htrace hcross
  have hball₀ : ∀ x ∈ J, ∀ O ∈ 𝓝 x,
      ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
        0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
          MapsTo g (Metric.ball c r) (K₀.space ∩ O) ∧ g c = x := by
    intro x hx O hO
    exact hK₀.exists_surface_ball_chart_of_notMem_boundaryComplex
      (hJ₀ hx) (fun hb => disjoint_left.mp hBd₀ hx hb) hO
  have hball₁ : ∀ x ∈ J, ∀ O ∈ 𝓝 x,
      ∃ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ) (g : EuclideanSpace ℝ (Fin 2) → E),
        0 < r ∧ ContinuousOn g (Metric.ball c r) ∧ InjOn g (Metric.ball c r) ∧
          MapsTo g (Metric.ball c r) (K₁.space ∩ O) ∧ g c = x := by
    intro x hx O hO
    exact hK₁.exists_surface_ball_chart_of_notMem_boundaryComplex
      (hJ₁ hx) (fun hb => disjoint_left.mp hBd₁ hx hb) hO
  obtain ⟨R, hRK, hRfin, hJR, ⟨chain⟩⟩ :=
    exists_interior_crossing_cell_chain K hK hdim hJ (subset_inter hJ₀ hJ₁) hJK
      hcross hball₀ hball₁ hN hJN (fun _ hx => htrace ⟨hx.1, hNU hx.2⟩)
  let := hRfin.to_subtype
  have hΓint : (PiecewiseLinear.restrict R J).space ⊆ interior R.space := by
    rw [hJR, hRK.space_eq]
    exact hJK
  have hNX := inter_eq_on_subset hNU hfrontX
  have hNY := inter_eq_on_subset hNU hfrontY
  obtain ⟨f, hf, hends, hpages, haxis, hfirst, hsecond, hCN, hJint⟩ :=
    chain.exists_untwisted_page_diagram (restrict_faces_subset R J) hΓint
      hNX hNY hNW₀ hNW₁ hP₀ hP₂ hP₁ hP₃
      (fun x hx => hcross x (hJR.subset hx))
      (fun x hx => hball₀ x (hJR.subset hx))
      (fun x hx => hball₁ x (hJR.subset hx)) hX hY hregX hregY
  let C := (derivedNeighborhood R (PiecewiseLinear.restrict R J)).space
  have hCW₀ : C ∩ W₀ = C ∩ frontier X :=
    (inter_eq_on_subset hCN hNW₀).symm.trans (inter_eq_on_subset hCN hNX)
  have hCW₁ : C ∩ W₁ = C ∩ frontier Y :=
    (inter_eq_on_subset hCN hNW₁).symm.trans (inter_eq_on_subset hCN hNY)
  refine ⟨R, f, hRK, hRfin, hJR, hf, hends, haxis.trans hJR,
    hfirst.trans (inter_eq_on_subset hCN hNX),
    hsecond.trans (inter_eq_on_subset hCN hNY), ?_, hCN.trans hNU, hJR.symm.subset.trans hJint⟩
  intro i
  rw [hpages i]
  change C ∩ P i = C ∩
    ![frontier X ∩ Y, frontier Y ∩ X, frontier X \ interior Y, frontier Y \ interior X] i
  fin_cases i
  · change C ∩ P 0 = C ∩ (frontier X ∩ Y)
    rw [hP₀, ← inter_assoc, hCW₀, inter_assoc]
  · change C ∩ P 1 = C ∩ (frontier Y ∩ X)
    rw [hP₁, ← inter_assoc, hCW₁, inter_assoc]
  · change C ∩ P 2 = C ∩ (frontier X \ interior Y)
    rw [hP₂, ← inter_sdiff_assoc, hCW₀, inter_sdiff_assoc]
  · change C ∩ P 3 = C ∩ (frontier Y \ interior X)
    rw [hP₃, ← inter_sdiff_assoc, hCW₁, inter_sdiff_assoc]

end DifferentialGeometry.Topology.PiecewiseLinear
