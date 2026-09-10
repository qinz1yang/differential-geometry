import DifferentialGeometry.Topology.Manifold.BoundaryCollar.HeightStrip
import DifferentialGeometry.Topology.Manifold.Boundary.RegularBand
import DifferentialGeometry.Topology.Collar.Superlevel

set_option autoImplicit false
noncomputable section
open Set Function Manifold Topology TopologicalSpace
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace DifferentialGeometry.Manifold.Boundary


theorem exists_small_superlevel_homeomorph
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [CompactSpace M]
    {V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y}
    (hV : ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
      (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)))
    (hpos : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
      0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V p))
    (N : Opens M) (hKN : (𝓡∂ (n + 1)).boundary M ⊆ N)
    {r : M → ℝ} (hr : MDifferentiable (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r)
    (hrzero : ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M, r p = 0)
    (hrpos : ∀ x, (𝓡∂ (n + 1)).IsInteriorPoint x → 0 < r x)
    (hunit : ∀ y ∈ N, (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r y) (V y) = (1 : ℝ)) :
    ∃ η : ℝ, 0 < η ∧
      (∀ x, mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) r x = 0 → η < r x) ∧
      ∀ a : ℝ, a ≤ η → Nonempty (M ≃ₜ {x | a ≤ r x}) := by
  have hK : IsCompact ((𝓡∂ (n + 1)).boundary M) :=
    ((𝓡∂ (n + 1)).isClosed_boundary (n := ∞) (by simp)).isCompact
  obtain ⟨ε,hε,c,hc,_,_,hheight,_,δ,hδ,hδε,hopen,hBimage⟩ :=
    BoundaryCollar.exists_smooth_unit_height_boundary_strip hK hV hpos N hKN hr hrzero hunit
  let : CompactSpace (BoundaryManifold (𝓡∂ (n + 1)) M) := isCompact_iff_compactSpace.mp hK
  let W : Opens M := ⟨(c '' {q | (q.2 : ℝ) < δ}) ∩ N,hopen.inter N.isOpen⟩
  have hBW : (𝓡∂ (n + 1)).boundary M ⊆ W := fun x hx => ⟨hBimage hx,hKN hx⟩
  obtain ⟨ζ,hζ,hsmall,hcritical,_⟩ := exists_regular_boundary_band hr.continuous hrpos W.isOpen hBW
    (fun y hy => hunit y hy.2)
  let η : ℝ := min (ζ/2) (δ/4)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηζ : η < ζ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hηδ : 2 * η < δ := by
    have hh : η ≤ δ/4 := min_le_right _ _
    linarith
  refine ⟨η,hη,(fun x hx => hηζ.trans (hcritical x hx)),?_⟩
  intro a ha
  have haδ : 2 * a < δ := lt_of_le_of_lt (mul_le_mul_of_nonneg_left ha (by norm_num)) hηδ
  have houtside : ∀ x ∉ range c, a ≤ r x := by
    intro x hx
    by_contra hn
    have hxr : r x ≤ ζ := (lt_of_not_ge hn).le.trans (ha.trans hηζ.le)
    have hw : x ∈ W := hsmall hxr
    exact hx (image_subset_range _ _ hw.1)
  obtain ⟨h,_⟩ := DifferentialGeometry.Topology.Collar.exists_homeomorph_superlevel_of_collar c hc.isEmbedding
    haδ hδε.le hopen hheight houtside
  exact ⟨h⟩

end DifferentialGeometry.Manifold.Boundary
