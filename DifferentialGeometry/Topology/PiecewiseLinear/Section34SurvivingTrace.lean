import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem IsAnnulusOn.image_inter_frontier_nonempty_of_eqOn_ends {M : Type*} [TopologicalSpace M]
    {A A₀ A₁ B : Set M} (hA : IsAnnulusOn A A₀ A₁) {φ : M → M}
    (hφ : ContinuousOn φ A) (hfix : EqOn φ id (A₀ ∪ A₁))
    (hzero : A₀ ⊆ B) (hone : Disjoint A₁ B) : (φ '' A ∩ frontier B).Nonempty := by
  by_contra hn
  have hcover : φ '' A ⊆ interior B ∪ interior Bᶜ := by
    rw [← compl_frontier_eq_union_interior]
    intro x hx hxfront
    exact hn ⟨x, hx, hxfront⟩
  have hconn := hA.isConnected.isPreconnected.image φ hφ
  rcases hconn.subset_or_subset isOpen_interior isOpen_interior
    (disjoint_compl_right.mono interior_subset interior_subset) hcover with hin | hout
  · obtain ⟨x, hx⟩ := hA.ends_nonempty.2
    have hxφ : x ∈ φ '' A := ⟨x, hA.second_subset hx, hfix (Or.inr hx)⟩
    exact disjoint_left.mp hone hx (interior_subset (hin hxφ))
  · obtain ⟨x, hx⟩ := hA.ends_nonempty.1
    have hxφ : x ∈ φ '' A := ⟨x, hA.first_subset hx, hfix (Or.inl hx)⟩
    exact interior_subset (hout hxφ) (hzero hx)

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

theorem section34_modified_first_boundary_trace_nonempty
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e₀ : Section34EdgeIndex 𝒦 𝒦') (φ : M₂ ≃ₜ M₂)
    (hfix : EqOn φ id (G (ends e₀).1 '' (Ab₀ e₀ ∪ Ab₁ e₀))) :
    (φ '' (G (ends e₀).1 '' CpBd (ends e₀).1) ∩ G (ends e₀).2 '' CpBd (ends e₀).2).Nonempty := by
  have hann := (section34_piercing_annuli hprep hpack e₀).1
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, hside, -, -, hG, -⟩ := hpack
  rw [image_union] at hfix
  obtain ⟨x, hx, hxfront⟩ := hann.image_inter_frontier_nonempty_of_eqOn_ends φ.continuous.continuousOn
    hfix ((hside e₀).1.trans interior_subset) (hside e₀).2
  refine ⟨x, image_mono (image_mono ((hAa e₀).1 ▸ inter_subset_left)) hx, ?_⟩
  rwa [← ((hCp (ends e₀).2).image (hG (ends e₀).2)).boundary_eq_frontier] at hxfront

end DifferentialGeometry.Topology.PiecewiseLinear
