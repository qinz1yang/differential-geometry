import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnulusFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSideConnectivity

open Set

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

theorem section34_first_rims_subset_inner_frontier
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') :
    G (ends e).1 '' (Ab₀ e ∪ Ab₁ e) ⊆ frontier (Tp e) := by
  have hann := (section34_piercing_annuli hprep hpack e).1
  have heq := section34_first_annulus_eq_boundary_inter_tube hprep hpack e
  obtain ⟨-, -, -, -, hCp, -⟩ := hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := hpack
  obtain ⟨hc⟩ := ((hCp (ends e).1).image (hG (ends e).1)).nonempty_chartedSpace_boundary
  let _ := hc
  have hdis := hann.ends_disjoint_interior_of_inter heq
  rw [image_union]
  intro x hx
  have hxT : x ∈ Tp e := (heq.subset ((union_subset hann.first_subset hann.second_subset) hx)).2
  exact ⟨subset_closure hxT, disjoint_left.mp hdis hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
