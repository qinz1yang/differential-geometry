import DifferentialGeometry.Topology.PiecewiseLinear.Section34SeamMarkedBandFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentCollaredFillingCylinder
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentPairedFillingSeamNeighborhood

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

theorem section34_current_seam_marked_band_filling
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j) {D F : Set M₂}
    (Ψ : M₂ ≃ₜ M₂) (hfix : ∀ x ∈ Pg e i ∪ Pg e j, Ψ =ᶠ[𝓝 x] id)
    (hcellB : IsPLCellOn 3 (Ψ '' (G (ends e).2 '' Cp (ends e).2))
      (Ψ '' (G (ends e).2 '' CpBd (ends e).2)))
    (hfill : Section34FaceAlignedBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (G (ends e).1 '' CpBd (ends e).1) (Ψ '' (G (ends e).2 '' CpBd (ends e).2))
      (interior (Sp e)) D F
      (Pg e i) (Pg e j)) :
    Section34SeamMarkedBandFilling
      (G (ends e).1 '' Cc (ends e).1) (G (ends e).1 '' Cp (ends e).1)
      (Ψ '' (G (ends e).2 '' Cp (ends e).2))
      (G (ends e).1 '' CpBd (ends e).1) (Ψ '' (G (ends e).2 '' CpBd (ends e).2))
      (Sp e) (interior (Sp e)) D F (Pg e i) (Pg e j) := by
  have hseams := hfill.seams_subset_faces
  obtain ⟨hF, hD, hDF⟩ := hfill.face_annuli_and_intersection
  obtain ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, hR, hRP, hsolid,
    hg, hends, hside, hfront, hT, hfirst, hsecond, hcontact, hposition, ha, hinj,
    hzero, hone, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, hinter, hface₀, hface₁⟩ := id hfill
  let _ : Finite R.faces := hRfin.to_subtype
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, hSnCc, -⟩ := id hprep
  obtain ⟨-, -, -, htube, -, -, -, -, -, -, hGp, -⟩ := id hpack
  have hcellA := (hCp (ends e).1).image (hGp (ends e).1)
  have hSpP : Sp e ⊆ u '' P := by
    rw [hcell, (htube e).1]
    exact image_mono (hSnCc e _ (Or.inl rfl))
  have hRint : R.space ⊆ interior P := by
    intro x hx
    have hux : u x ∈ interior (u '' P) := interior_mono hSpP (hT ⟨x, hx, rfl⟩)
    rw [← hu.image_interior] at hux
    obtain ⟨y, hy, hyx⟩ := hux
    exact hu.injOn (interior_subset hy) (hRP hx) hyx ▸ hy
  have hclosedR : IsClosed R.space := (isPolyhedron_space R).isClosed
  have hregR : closure (interior R.space) = R.space :=
    (closure_minimal interior_subset hclosedR).antisymm
      (hR.subset_closure_interior_space (by simp))
  have hconnR : IsConnected (interior R.space) :=
    (isConnected_interior_space_and_compl (Set.toFinite R.faces) hR
      (hsolid.1.isConnected_frontier hclosedR) hsolid.1.interior_nonempty).1
  have hJO : Pg e i ∪ Pg e j ⊆ interior (Sp e) := by
    intro x hx
    exact hT (hsecond.symm.subset (hseams hx).1).2
  obtain ⟨N, C, f, α, β, hN, -, hCdis, htarget, hcf⟩ :=
    exists_section34_current_paired_filling_seam_neighborhoods hprep hpack e hi hj hij hP hu
      hcell Ψ hfix hcellB hRint hclosedR hregR hconnR hfront hfirst hsecond hseams
      isOpen_interior hJO
  have hfamily : ∀ k,
      IsPolyhedron (C k) ∧ C k ⊆ interior P ∧
      IsCylindricalDiagram (f k) spliceSquare (C k) ∧
      (∀ x ∈ spliceSquare, f k (x, 0) = f k (x, 1)) ∧
      u '' (f k '' section34MarkedAxis) = ![Pg e i, Pg e j] k ∧
      u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
        u '' C k ∩ G (ends e).1 '' CpBd (ends e).1 ∧
      u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
        u '' C k ∩ Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∧
      (∀ l : Fin 4, u '' (f k '' section34MarkedRibbon l) = u '' C k ∩
        ![G (ends e).1 '' CpBd (ends e).1 ∩ Ψ '' (G (ends e).2 '' Cp (ends e).2),
          Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∩ G (ends e).1 '' Cp (ends e).1,
          G (ends e).1 '' CpBd (ends e).1 \ interior (Ψ '' (G (ends e).2 '' Cp (ends e).2)),
          Ψ '' (G (ends e).2 '' CpBd (ends e).2) \ interior (G (ends e).1 '' Cp (ends e).1)] l) ∧
      u '' C k ⊆ interior (Sp e) ∧ ![Pg e i, Pg e j] k ⊆ interior (u '' C k) ∧
      f k '' (section34CrossingQuadrant (α k) (β k) ×ˢ Icc (0 : ℝ) 1) = C k ∩ R.space := by
    intro k
    have hindex : Pg e (![i, j] k) = ![Pg e i, Pg e j] k := by fin_cases k <;> rfl
    obtain ⟨hC, hCP, hf, hfends, haxis, hA, hB, hpages, hCN, hJC, hquad⟩ := hcf k
    rw [hindex] at haxis hJC
    exact ⟨hC, hCP, hf, hfends, haxis, hA, hB, hpages, hCN.trans (hN k).2.2, hJC, hquad⟩
  obtain ⟨c, L, W, ρ, H, hcollar⟩ :=
    exists_collared_filling_cylinder_of_cell_contacts hcellA hcellB hP hu R hR
      hsolid.1 hRint hT hfront hfirst hsecond hseams hF hD hDF
      (fun k => (hfamily k).1) (fun k => (hfamily k).2.1)
      (fun k => (hfamily k).2.2.1) (fun k => (hfamily k).2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.2.2.1) (fun k => (hfamily k).2.2.2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.2.2.2.2.2.2.1)
      (fun k => (hfamily k).2.2.2.1) α β
      (fun k => (hfamily k).2.2.2.2.2.2.2.2.2.2) hCdis hg hends hside
  have hcorrection := exists_actual_paired_seam_correction hu.injOn R hR hRP hg hends
    hside hfirst hsecond hδ₀ hδ₁ hδ₀₀ hδ₀₁ hδ₁₀ hδ₁₁ hcover hinter hface₀ hface₁
    (by
      intro k
      fin_cases k
      · exact hzero
      · exact hone)
    (fun k => (hfamily k).2.1.trans interior_subset)
    (fun k => (hfamily k).2.2.1) (fun k => (hfamily k).2.2.2.1)
    (fun k => (hfamily k).2.2.2.2.1) (fun k => (hfamily k).2.2.2.2.2.1)
    (fun k => (hfamily k).2.2.2.2.2.2.1) α β
    (fun k => (hfamily k).2.2.2.2.2.2.2.2.2.2)
  obtain ⟨hbase, hH, hHends, hHeq, hshell, hsupport, hc, hc1, hLfin, hL,
    hLB, hJL, hLnhds, haxisModel, hW, hWP, hWSp, hρ, hρzero, htrace,
    hpositive, hread, hfull, hlevels⟩ := hcollar
  exact ⟨P, u, R, g, a, A₀, A₁, δ₀, δ₁, hP, hu, hcell, hRfin, hR, hRP, hsolid,
    hg, hends, hside, hfront, hT, hfirst, hsecond, hcontact, hposition, ha, hinj,
    hzero, hone, hδ₀, hδ₁, hδ₀₀, hδ₀₁, hδ₁₀, hδ₁₁, hcover, hinter, hface₀, hface₁,
    C, f, α, β, hCdis, htarget, hfamily, c, L, W, ρ, H,
    hbase, hH, hHends, hHeq, hshell, hsupport, hc, hc1, hLfin, hL,
    hLB, hJL, hLnhds, haxisModel, hW, hWP, hWSp, hρ, hρzero, htrace,
    hpositive, hread, hfull, hlevels, hcorrection⟩

end DifferentialGeometry.Topology.PiecewiseLinear
