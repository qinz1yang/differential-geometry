import DifferentialGeometry.Topology.PiecewiseLinear.BallUnionFrontier
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingGenerators

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

theorem section34_piercing_trace_nonempty_of_sides
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hG : ∀ w, IsPLHomeomorphInto 3 (G w) (Cp w)) (e : Section34EdgeIndex 𝒦 𝒦')
    (hboundary : G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' CpBd (ends e).2 ⊆
      G (ends e).2 '' Bb e)
    (hside : G (ends e).1 '' Ab₀ e ⊆ G (ends e).2 '' Cp (ends e).2 ∧
      Disjoint (G (ends e).1 '' Ab₁ e) (G (ends e).2 '' Cp (ends e).2)) :
    (G (ends e).1 '' Aa e ∩ G (ends e).2 '' Bb e).Nonempty := by
  obtain ⟨-, -, -, -, hCp, -, -, -, -, -, -, -, -, -, hAa, -⟩ := hprep
  have hABd : Aa e ⊆ CpBd (ends e).1 := (hAa e).1 ▸ inter_subset_left
  have hACp := hABd.trans (hCp _).boundary_subset
  have hconn := (hAa e).2.isConnected.image _ ((hG _).continuousOn.mono hACp)
  obtain ⟨x, hx⟩ := (hAa e).2.ends_nonempty.1.image (G (ends e).1)
  obtain ⟨y, hy⟩ := (hAa e).2.ends_nonempty.2.image (G (ends e).1)
  have hmeet : (G (ends e).1 '' Aa e ∩ G (ends e).2 '' Cp (ends e).2).Nonempty :=
    ⟨x, image_mono (hAa e).2.first_subset hx, hside.1 hx⟩
  by_contra hnone
  have havoid : Disjoint (G (ends e).1 '' Aa e)
      (frontier (G (ends e).2 '' Cp (ends e).2)) := by
    rw [← ((hCp (ends e).2).image_boundary_interior (hG (ends e).2)).1]
    exact disjoint_left.mpr fun z hzA hzB =>
      hnone ⟨z, hzA, hboundary ⟨image_mono hABd hzA, hzB⟩⟩
  have hsub := IsPreconnected.subset_of_disjoint_frontier hconn.isPreconnected hmeet havoid
  exact disjoint_left.mp hside.2 hy (hsub (image_mono (hAa e).2.second_subset hy))

end DifferentialGeometry.Topology.PiecewiseLinear
