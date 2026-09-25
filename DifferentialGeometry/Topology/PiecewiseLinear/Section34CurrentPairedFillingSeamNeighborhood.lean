import DifferentialGeometry.Topology.PiecewiseLinear.Section34FaceAlignedBandFilling
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CurrentFillingCrossingNeighborhood

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

theorem exists_section34_current_paired_filling_seam_neighborhoods
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦')
    {i j : ℕ} (hi : i < cnt e) (hj : j < cnt e) (hij : i ≠ j)
    {P : Set (EuclideanSpace ℝ (Fin 3))} {u : EuclideanSpace ℝ (Fin 3) → M₂}
    (hP : IsPLBall 3 P) (hu : IsPLHomeomorphInto 3 u P)
    (hmodel : u '' P = G (ends e).1 '' Cc (ends e).1)
    (Ψ : M₂ ≃ₜ M₂) (hfix : ∀ x ∈ Pg e i ∪ Pg e j, Ψ =ᶠ[𝓝 x] id)
    (hcellB : IsPLCellOn 3 (Ψ '' (G (ends e).2 '' Cp (ends e).2))
      (Ψ '' (G (ends e).2 '' CpBd (ends e).2)))
    {R : Set (EuclideanSpace ℝ (Fin 3))} (hRint : R ⊆ interior P)
    (hclosedR : IsClosed R) (hregR : closure (interior R) = R)
    (hconnR : IsConnected (interior R)) {D F : Set M₂}
    (hfront : u '' frontier R = D ∪ F)
    (hcontactA : G (ends e).1 '' CpBd (ends e).1 ∩ u '' R = F)
    (hcontactB : Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∩ u '' R = D)
    (hJDF : Pg e i ∪ Pg e j ⊆ D ∩ F)
    {O : Set M₂} (hO : IsOpen O) (hJO : Pg e i ∪ Pg e j ⊆ O) :
    ∃ (N : Fin 2 → Set M₂) (C : Fin 2 → Set (EuclideanSpace ℝ (Fin 3)))
      (f : Fin 2 → (ℝ × ℝ) × ℝ → EuclideanSpace ℝ (Fin 3)) (a b : Fin 2 → Bool),
      (∀ k, IsOpen (N k) ∧ Pg e (![i, j] k) ⊆ N k ∧ N k ⊆ O) ∧
      Disjoint (N 0) (N 1) ∧ Disjoint (C 0) (C 1) ∧
      Disjoint (u '' C 0) (u '' C 1) ∧ ∀ k,
      IsPolyhedron (C k) ∧ C k ⊆ interior P ∧ IsCylindricalDiagram (f k) spliceSquare (C k) ∧
      (∀ x ∈ spliceSquare, f k (x, 0) = f k (x, 1)) ∧
      u '' (f k '' section34MarkedAxis) = Pg e (![i, j] k) ∧
      u '' (f k '' (section34MarkedRibbon 0 ∪ section34MarkedRibbon 2)) =
        u '' C k ∩ G (ends e).1 '' CpBd (ends e).1 ∧
      u '' (f k '' (section34MarkedRibbon 1 ∪ section34MarkedRibbon 3)) =
        u '' C k ∩ Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∧
      (∀ l : Fin 4, u '' (f k '' section34MarkedRibbon l) = u '' C k ∩
        ![G (ends e).1 '' CpBd (ends e).1 ∩ Ψ '' (G (ends e).2 '' Cp (ends e).2),
          Ψ '' (G (ends e).2 '' CpBd (ends e).2) ∩ G (ends e).1 '' Cp (ends e).1,
          G (ends e).1 '' CpBd (ends e).1 \ interior (Ψ '' (G (ends e).2 '' Cp (ends e).2)),
          Ψ '' (G (ends e).2 '' CpBd (ends e).2) \ interior (G (ends e).1 '' Cp (ends e).1)] l) ∧
      u '' C k ⊆ N k ∧ Pg e (![i, j] k) ⊆ interior (u '' C k) ∧
      f k '' (section34CrossingQuadrant (a k) (b k) ×ˢ Icc (0 : ℝ) 1) = C k ∩ R := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hpoly, hdis, -⟩ := id hpack
  have hclosed (k : ℕ) (hk : k < cnt e) : IsClosed (Pg e k) := by
    obtain ⟨Q, -⟩ := (hpoly e k hk).1
    exact Q.piece.isCompact.isClosed
  obtain ⟨V₀, V₁, hV₀, hV₁, hJV₀, hJV₁, hVdis⟩ :=
    normal_separation (hclosed i hi) (hclosed j hj) (hdis e i hi j hj hij)
  let N : Fin 2 → Set M₂ := ![O ∩ V₀, O ∩ V₁]
  have hN (k : Fin 2) : IsOpen (N k) ∧ Pg e (![i, j] k) ⊆ N k ∧ N k ⊆ O := by
    fin_cases k
    · exact ⟨hO.inter hV₀, fun x hx => ⟨hJO (Or.inl hx), hJV₀ hx⟩, inter_subset_left⟩
    · exact ⟨hO.inter hV₁, fun x hx => ⟨hJO (Or.inr hx), hJV₁ hx⟩, inter_subset_left⟩
  have hNdis : Disjoint (N 0) (N 1) := hVdis.mono inter_subset_right inter_subset_right
  have hindex (k : Fin 2) : ![i, j] k < cnt e := by
    fin_cases k
    · exact hi
    · exact hj
  have hfaces (k : Fin 2) : Pg e (![i, j] k) ⊆ D ∩ F := by
    fin_cases k
    · exact subset_union_left.trans hJDF
    · exact subset_union_right.trans hJDF
  have hfix' (k : Fin 2) : ∀ x ∈ Pg e (![i, j] k), Ψ =ᶠ[𝓝 x] id := by
    fin_cases k
    · exact fun x hx => hfix x (Or.inl hx)
    · exact fun x hx => hfix x (Or.inr hx)
  have hex (k : Fin 2) := exists_section34_current_filling_seam_neighborhood hprep hpack e
    (hindex k) hP hu hmodel Ψ (hfix' k) hcellB hRint hclosedR hregR hconnR
    hfront hcontactA hcontactB (hfaces k) (hN k).1 (hN k).2.1
  choose C f a b hcf using hex
  have hCN (k : Fin 2) : u '' C k ⊆ N k := by
    obtain ⟨-, -, -, -, -, -, -, -, hCN, -⟩ := hcf k
    exact hCN
  have htarget : Disjoint (u '' C 0) (u '' C 1) := hNdis.mono (hCN 0) (hCN 1)
  exact ⟨N, C, f, a, b, hN, hNdis,
    disjoint_left.mpr (fun x hx hy => disjoint_left.mp htarget
      (mem_image_of_mem u hx) (mem_image_of_mem u hy)), htarget, hcf⟩

end DifferentialGeometry.Topology.PiecewiseLinear
