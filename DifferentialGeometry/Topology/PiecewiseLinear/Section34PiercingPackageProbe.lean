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
  have exists_auxiliary_scales_preserving_piercing_sides :
      ∃ δ : Section34VertexIndex 𝒦 𝒦' → ℝ,
        (∀ w, 0 < δ w) ∧ (∀ w, δ w < ε w) ∧
        ∀ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
          (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) →
          (∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w) →
          (∀ e, G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
            interior (G (ends e).1 '' Tn e)) ∧
          (∀ e, G (ends e).1 '' Ab₀ e ⊆ interior (G (ends e).2 '' Cp (ends e).2)) ∧
          (∀ e, G (ends e).2 '' Bb e ⊆ interior (G (ends e).1 '' Sn e)) ∧
          (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
            ∀ z ∈ G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1,
              z ∉ G (ends e).1 '' Tn e →
              z ∈ connectedComponentIn
                (G (ends e).2 '' Bb e ∩ G (ends e).1 '' Cp (ends e).1) y₀) ∧
          (∀ e, ∃ y₀ ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
            ∀ z ∈ G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1,
              z ∉ G (ends e).1 '' Tn e →
              z ∈ connectedComponentIn
                (G (ends e).2 '' Bb e \ G (ends e).1 '' Cp (ends e).1) y₀) := by
    sorry
  obtain ⟨δ, hδ, hδε, hsides⟩ := exists_auxiliary_scales_preserving_piercing_sides
  obtain ⟨-, hcc, hsubs, hchart, -⟩ := id hprep
  obtain ⟨G₀, hG₀, hG₀dist⟩ := h341.exists_chart_local_cell_approximations hh Cc CcBd hcc
    (fun w => (hsubs w).2.2) hchart (fun w => δ w / 3)
    (fun w => div_pos (hδ w) (by norm_num))
  let A (F : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e : Section34EdgeIndex 𝒦 𝒦') :=
    F (ends e).1 '' Aa e
  let B (F : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (e : Section34EdgeIndex 𝒦 𝒦') :=
    F (ends e).2 '' Bb e
  have exists_relative_crossing_vertex_approximations :
      ∃ G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
        (∀ w, IsPLHomeomorphInto 3 (G w) (Cc w)) ∧
        (∀ w, ∀ x ∈ Cc w, dist (G w x) (G₀ w x) < δ w / 3) ∧
        ∀ e, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂,
          A G e ∩ B G e ⊆ c.source ∧
          IsPolyhedron (c '' (A G e ∩ c.source) ∩ c '' (B G e ∩ c.source)) ∧
          (∀ x ∈ c '' (A G e ∩ c.source) ∩ c '' (B G e ∩ c.source),
            HasPLCrossingAt (c '' (A G e ∩ c.source)) (c '' (B G e ∩ c.source)) x) ∧
          ∀ x ∈ c '' (A G e ∩ c.source) ∩ c '' (B G e ∩ c.source),
            ∃ (V : Set (EuclideanSpace ℝ (Fin 3)))
              (φ : EuclideanSpace ℝ (Fin 3) → ℝ × ℝ × ℝ) (ρ : ℝ),
              IsOpen V ∧ x ∈ V ∧ 0 < ρ ∧
              IsPLHomeomorphOn φ V (Metric.ball 0 ρ) ∧ φ x = 0 ∧
              ∀ y ∈ V, (y ∈ c '' (A G e ∩ c.source) ↔ (φ y).2.2 = 0) ∧
                (y ∈ c '' (B G e ∩ c.source) ↔ (φ y).2.1 = 0) := by
    sorry
  obtain ⟨G, hG, hGG₀, htraceCharts⟩ := exists_relative_crossing_vertex_approximations
  have hGδ : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < δ w := by
    intro w x hx
    have ht := dist_triangle (G w x) (G₀ w x) (h x)
    linarith [hGG₀ w x hx, hG₀dist w x hx, hδ w]
  have hGdist : ∀ w, ∀ x ∈ Cc w, dist (G w x) (h x) < ε w :=
    fun w x hx => (hGδ w x hx).trans (hδε w)
  obtain ⟨htraceInside, hAb₀Inside, hBbInside, hcomponentInside, hcomponentOutside⟩ :=
    hsides G hG hGδ
  obtain ⟨-, -, -, -, hcp, -⟩ := id hprep
  have hGp : ∀ w, IsPLHomeomorphInto 3 (G w) (Cp w) := fun w =>
    (hG w).mono_of_isPLCellOn (hcp w) (hsubs w).2.1
  have hne := section34_piercing_trace_nonempty hprep hGp hGdist hAb₀Inside
  have hfamily (e : Section34EdgeIndex 𝒦 𝒦') :
      ∃ (cnt : ℕ) (Pg : ℕ → Set M₂), 0 < cnt ∧ A G e ∩ B G e = ⋃ i < cnt, Pg i ∧
        (∀ i < cnt, IsPolyhedralSphere (n := 3) 1 (Pg i) ∧ Pg i ⊆ A G e ∩ B G e) ∧
        (∀ i < cnt, ∀ j < cnt, i ≠ j → Disjoint (Pg i) (Pg j)) ∧
        ∀ y ∈ A G e ∩ B G e, ∃ c ∈ (plGroupoid 3).maximalAtlas M₂, y ∈ c.source ∧
          HasPLCrossingAt (c '' (A G e ∩ c.source)) (c '' (B G e ∩ c.source)) (c y) := by
    obtain ⟨c, hc, hsource, hpoly, hcross, hline⟩ := htraceCharts e
    exact exists_positive_finite_piercing_circle_family c hc hsource hpoly hcross hline (hne e)
  choose cnt Pg hcnt hcover hcircles hdisj hcross using hfamily
  let Sp (e : Section34EdgeIndex 𝒦 𝒦') := G (ends e).1 '' Sn e
  let Tp (e : Section34EdgeIndex 𝒦 𝒦') := G (ends e).1 '' Tn e
  refine ⟨Sp, Tp, cnt, Pg, G, ?_, hGdist⟩
  exact piercing_conditions_of_crossings_and_margins hframe hQlfU hprep hG hGdist
    (fun _ => ⟨rfl, rfl⟩) htraceInside hAb₀Inside hBbInside hcomponentInside hcomponentOutside
    (fun e => ⟨hcnt e, hcover e⟩) hcircles hdisj hcross

end Leaves

end DifferentialGeometry.Topology.PiecewiseLinear
