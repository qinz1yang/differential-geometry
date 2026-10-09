import DifferentialGeometry.Topology.PiecewiseLinear.Section34ActualFillingCrossingNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentFillingRegions
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingPreservation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem exists_section34_current_filling_seam_neighborhood
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hP : IsPLBall 3 P) (hu : IsPLHomeomorphInto 3 u P)
    (hmodel : u '' P = G (ends e).1 '' Cc (ends e).1)
    (Ψ : M₂ ≃ₜ M₂) (hfix : ∀ x ∈ Pg e i, Ψ =ᶠ[𝓝 x] id)
    (hcellB : IsPLCellOn 3 (Ψ '' (G (ends e).2 '' Cp (ends e).2))
      (Ψ '' (G (ends e).2 '' CpBd (ends e).2)))
    {R : Set (EuclideanSpace ℝ (Fin 3))} (hRint : R ⊆ interior P)
    (hclosedR : IsClosed R) (hregR : closure (interior R) = R)
    (hconnR : IsConnected (interior R)) {D F : Set M₂}
    (hfront : u '' frontier R = D ∪ F)
    (hcontactA : G (ends e).1 '' CpBd (ends e).1 ∩ u '' R = F)
    (hcontactB : Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∩ u '' R = D)
    (hJDF : Pg e i ⊆ D ∩ F)
    {O : Set M₂} (hO : IsOpen O) (hJO : Pg e i ⊆ O) :
    ∃ (C : Set (EuclideanSpace ℝ (Fin 3)))
      (f : (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (a b : Bool),
      IsPolyhedron C ∧ C ⊆ interior P ∧ IsCylindricalDiagram f spliceSquare C ∧
      (∀ x ∈ spliceSquare, f (x, 0) = f (x, 1)) ∧
      u '' (f '' section34MarkedAxis) = Pg e i ∧
      u '' (f '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
        u '' C ∩ G (ends e).1 '' CpBd (ends e).1 ∧
      u '' (f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
        u '' C ∩ Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∧
      (∀ j : Fin 4, u '' (f '' section34MarkedRibbon j) = u '' C ∩
        ![G (ends e).1 '' CpBd (ends e).1 ∩ Ψ '' (G (ends e).2 '' Cp (ends e).2),
          Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∩ G (ends e).1 '' Cp (ends e).1,
          G (ends e).1 '' CpBd (ends e).1 \ interior (Ψ '' (G (ends e).2 '' Cp (ends e).2)),
          Ψ '' (G (ends e).2 '' CpBd (ends e).2) \ interior (G (ends e).1 '' Cp (ends e).1)] j) ∧
      u '' C ⊆ O ∧ Pg e i ⊆ interior (u '' C) ∧
      f '' (section34CrossingQuadrant a b ×ˢ Icc (0 : ℝ) 1) = C ∩ R := by
  let V : Set M₂ := interior {x | Ψ x = x}
  have hJV : Pg e i ⊆ V := fun x hx => mem_interior_iff_mem_nhds.mpr (hfix x hx)
  have hVfix : EqOn Ψ id V := fun _ hx =>
    interior_subset (s := {x | Ψ x = x}) hx
  obtain ⟨C, f, hC, hCP, hf, hends, haxis, hfirst, hsecond, hpages, hCV, hJC⟩ :=
    exists_section34_actual_crossing_neighborhood_in_model hprep hpack e hi hP hu hmodel
      (hO.inter isOpen_interior) (subset_inter hJO hJV)
  have hmem (B : Set M₂) {x : M₂} (hx : x ∈ u '' C) : x ∈ Ψ '' B ↔ x ∈ B := by
    have heq := Set.ext_iff.mp (Homeomorph.image_inter_of_eqOn Ψ (B := B) hVfix) x
    exact ⟨fun h => (heq.mp ⟨h, (hCV hx).2⟩).1,
      fun h => (heq.mpr ⟨h, (hCV hx).2⟩).1⟩
  have hsecondCurrent : u '' (f '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
      u '' C ∩ Ψ '' (G (ends e).2 '' CpBd (ends e).2) := by
    rw [hsecond]
    ext x
    exact and_congr_right (fun hx => (hmem _ hx).symm)
  have hpagesCurrent (j : Fin 4) : u '' (f '' section34MarkedRibbon j) = u '' C ∩
      ![G (ends e).1 '' CpBd (ends e).1 ∩ Ψ '' (G (ends e).2 '' Cp (ends e).2),
        Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∩ G (ends e).1 '' Cp (ends e).1,
        G (ends e).1 '' CpBd (ends e).1 \ interior (Ψ '' (G (ends e).2 '' Cp (ends e).2)),
        Ψ '' (G (ends e).2 '' CpBd (ends e).2) \ interior (G (ends e).1 '' Cp (ends e).1)] j := by
    rw [hpages j]
    ext x
    apply and_congr_right
    intro hx
    fin_cases j
    · exact Iff.rfl.and (hmem _ hx).symm
    · exact (hmem _ hx).symm.and Iff.rfl
    · change (x ∈ G (ends e).1 '' CpBd (ends e).1 ∧
          x ∉ interior (G (ends e).2 '' Cp (ends e).2)) ↔ _
      rw [← Ψ.image_interior]
      exact Iff.rfl.and (hmem _ hx).symm.not
    · exact (hmem _ hx).symm.and Iff.rfl
  obtain ⟨-, -, -, -, hCp, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGp, -⟩ := id hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  obtain ⟨-, hX, hY, -, -, -, -, -, -, -, -, hRX, hRY, hfrontR, hJR⟩ :=
    hu.filling_regions_of_cell_contacts hcellA hcellB hRint hclosedR hregR hconnR
      hfront hcontactA hcontactB hJDF
  have hregA : closure (interior (G (ends e).1 '' Cp (ends e).1)) =
      G (ends e).1 '' Cp (ends e).1 := by
    rw [← hcellA.sdiff_boundary_eq_interior]
    exact hcellA.closure_sdiff_boundary
  have hregB : closure (interior (Ψ '' (G (ends e).2 '' Cp (ends e).2))) =
      Ψ '' (G (ends e).2 '' Cp (ends e).2) := by
    rw [← hcellB.sdiff_boundary_eq_interior]
    exact hcellB.closure_sdiff_boundary
  have hfirst' := hfirst
  have hsecond' := hsecondCurrent
  have hpages' := hpagesCurrent
  rw [hcellA.boundary_eq_frontier] at hfirst' hpages'
  rw [hcellB.boundary_eq_frontier] at hsecond' hpages'
  obtain ⟨hmfirst, hmsecond, hmpages⟩ := hu.crossing_traces_of_image hP.isPolyhedron.isClosed
    hCP hf hcellA.isCompact.isClosed hcellB.isCompact.isClosed hregA hregB
    hfirst' hsecond' hpages'
  have haxisC : f '' section34MarkedAxis ⊆ C :=
    (image_mono ((section34_marked_axis_subset_ribbon 0).trans
      (section34_marked_ribbon_subset_cylinder 0))).trans hf.image_eq.subset
  have haxisR : f '' section34MarkedAxis ⊆ R := by
    intro x hx
    have hux := haxis.subset (mem_image_of_mem u hx)
    have hxR := hJR (mem_image_of_mem (Function.invFunOn u P) hux)
    rwa [hu.injOn.leftInvOn_invFunOn (interior_subset (hCP (haxisC hx)))] at hxR
  have haxisInt : f '' section34MarkedAxis ⊆ interior C := by
    intro x hx
    have hux := hJC (haxis.subset (mem_image_of_mem u hx))
    rw [← hu.image_interior_of_isCompact_subset_interior hC.isCompact hCP] at hux
    obtain ⟨y, hy, heq⟩ := hux
    have hyx := hu.injOn (interior_subset (hCP (interior_subset hy)))
      (interior_subset (hCP (haxisC hx))) heq
    exact hyx ▸ hy
  obtain ⟨a, b, -, -, hquadrant⟩ := hf.exists_filling_quadrant hends hmfirst hmsecond hmpages
    hX hY haxisInt haxisR hclosedR hregR hconnR.isPreconnected hRX hRY hfrontR
  exact ⟨C, f, a, b, hC, hCP, hf, hends, haxis, hfirst, hsecondCurrent, hpagesCurrent,
    hCV.trans inter_subset_left, hJC, hquadrant⟩

end DifferentialGeometry.Topology.PiecewiseLinear
