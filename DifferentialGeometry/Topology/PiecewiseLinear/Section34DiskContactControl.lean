import DifferentialGeometry.Topology.PiecewiseLinear.Section34DiskFillingTrace

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsPLCellOn.inter_frontier_eq_cap {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {C D F T : Set M}
    (hC : IsPLCellOn 3 C (D ∪ F)) (hCT : C ⊆ T) (hDT : D ⊆ interior T) :
    C ∩ frontier T = F ∩ frontier T := by
  apply Subset.antisymm
  · intro x hx
    have hxC : x ∈ frontier C := ⟨subset_closure hx.1, fun hi => hx.2.2 (interior_mono hCT hi)⟩
    rw [← hC.boundary_eq_frontier] at hxC
    rcases hxC with hxD | hxF
    · exact (hx.2.2 (hDT hxD)).elim
    · exact ⟨hxF, hx.2⟩
  · exact inter_subset_inter_left _ (subset_union_right.trans hC.boundary_subset)

theorem IsPLCellOn.inter_subset_interior_of_boundary_inter_subset {M : Type*}
    [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] {C D F B T : Set M}
    (hC : IsPLCellOn 3 C (D ∪ F)) (hCT : C ⊆ T) (hDT : D ⊆ interior T)
    (hFB : F ∩ B ⊆ interior T) : C ∩ B ⊆ interior T := by
  intro x hx
  by_contra hi
  have hxC : x ∈ frontier C := ⟨subset_closure hx.1, fun h => hi (interior_mono hCT h)⟩
  rw [← hC.boundary_eq_frontier] at hxC
  rcases hxC with hxD | hxF
  · exact hi (hDT hxD)
  · exact hi (hFB ⟨hxF, hx.2⟩)

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

theorem exists_section34_filling_with_interior_second_contact
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') {i : ℕ} (hi : i < cnt e)
    {D : Set M₂} (hD : IsPLCellOn 2 D (Pg e i))
    (hDT : D ⊆ G (ends e).2 '' Bb e ∩ interior (Tp e))
    (htrace : D ∩ G (ends e).1 '' CpBd (ends e).1 = Pg e i) :
    ∃ F C : Set M₂, IsPLCellOn 2 F (Pg e i) ∧ F ⊆ G (ends e).1 '' Aa e ∧
      IsPLCellOn 3 C (D ∪ F) ∧ C ⊆ Tp e ∧
      G (ends e).1 '' CpBd (ends e).1 ∩ C = F ∧
      closure (frontier C \ G (ends e).1 '' CpBd (ends e).1) = D ∧
      (C ⊆ G (ends e).1 '' Cp (ends e).1 ∨ C ∩ G (ends e).1 '' Cp (ends e).1 = F) ∧
      C ∩ frontier (Tp e) = F ∩ frontier (Tp e) ∧
      C ∩ G (ends e).2 '' CpBd (ends e).2 ⊆ interior (Tp e) := by
  obtain ⟨F, C, hF, hFA, hC, hCT, hmeet, hcap, hside⟩ :=
    exists_section34_filling_with_exact_first_trace hprep hpack e hi hD
      (hDT.trans (inter_subset_inter_right _ interior_subset)) htrace
  obtain ⟨-, -, -, -, -, -, hcross, -⟩ := hpack
  have hFB : F ∩ G (ends e).2 '' CpBd (ends e).2 ⊆ interior (Tp e) := by
    intro x hx
    exact (hcross e ⟨(hmeet.superset hx.1).1, hx.2⟩).2
  exact ⟨F, C, hF, hFA, hC, hCT, hmeet, hcap, hside,
    hC.inter_frontier_eq_cap hCT (hDT.trans inter_subset_right),
    hC.inter_subset_interior_of_boundary_inter_subset hCT (hDT.trans inter_subset_right) hFB⟩

end DifferentialGeometry.Topology.PiecewiseLinear
