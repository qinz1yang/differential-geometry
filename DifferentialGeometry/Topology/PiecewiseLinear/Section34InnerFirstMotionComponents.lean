import DifferentialGeometry.Topology.PiecewiseLinear.Section34CrossingOutsideDensity
import DifferentialGeometry.Topology.PiecewiseLinear.Section34TraceDeletionComponents

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

theorem section34_both_sides_nonempty_of_first_motion_fixed_near_crossing
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (φ : M₂ ≃ₜ M₂) {x : M₂}
    (hx : x ∈ G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' Bb e)
    (hfix : φ =ᶠ[𝓝 x] id) :
    (G (ends e).2 '' Bb e ∩ φ '' (G (ends e).1 '' Cp (ends e).1)).Nonempty ∧
      (G (ends e).2 '' Bb e \ φ '' (G (ends e).1 '' Cp (ends e).1)).Nonempty := by
  obtain ⟨O, hOeq, hO, hxO⟩ := eventually_nhds_iff.mp hfix
  obtain ⟨V, -, -, -, hxin⟩ := section34_crossing_inside_slice hprep hpack e hx
  obtain ⟨z, hzO, hz⟩ := mem_closure_iff.mp hxin O hO hxO
  obtain ⟨W, -, -, -, hxout⟩ := section34_crossing_outside_slice hprep hpack e hx
  obtain ⟨w, hwO, hw⟩ := mem_closure_iff.mp hxout O hO hxO
  refine ⟨⟨z, hz.1.1, z, interior_subset hz.1.2, hOeq z hzO⟩, ⟨w, hw.1.1, ?_⟩⟩
  rintro ⟨y, hy, hyw⟩
  have hyw' : y = w := φ.injective (hyw.trans (hOeq w hwO).symm)
  exact hw.1.2 (hyw' ▸ hy)

theorem section34_piercing_components_of_inner_first_motion
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) (e : Section34EdgeIndex 𝒦 𝒦') (φ : M₂ ≃ₜ M₂)
    (hfix : EqOn φ id (Tp e)ᶜ)
    (htrace : φ '' (G (ends e).1 '' CpBd (ends e).1) ∩ G (ends e).2 '' Bb e ⊆
      G (ends e).1 '' CpBd (ends e).1)
    (hnear : ∃ x ∈ G (ends e).1 '' CpBd (ends e).1 ∩ G (ends e).2 '' Bb e,
      φ =ᶠ[𝓝 x] id) :
    (∃ a ∈ G (ends e).2 '' Bb e ∩ φ '' (G (ends e).1 '' Cp (ends e).1),
      ∀ z ∈ G (ends e).2 '' Bb e ∩ φ '' (G (ends e).1 '' Cp (ends e).1), z ∉ Tp e →
        z ∈ connectedComponentIn
          (G (ends e).2 '' Bb e ∩ φ '' (G (ends e).1 '' Cp (ends e).1)) a) ∧
    ∃ b ∈ G (ends e).2 '' Bb e \ φ '' (G (ends e).1 '' Cp (ends e).1),
      ∀ z ∈ G (ends e).2 '' Bb e \ φ '' (G (ends e).1 '' Cp (ends e).1), z ∉ Tp e →
        z ∈ connectedComponentIn
          (G (ends e).2 '' Bb e \ φ '' (G (ends e).1 '' Cp (ends e).1)) b := by
  obtain ⟨x, hx, hgerm⟩ := hnear
  have hne := section34_both_sides_nonempty_of_first_motion_fixed_near_crossing
    hprep hpack e φ hx hgerm
  obtain ⟨-, -, -, -, hCp, -⟩ := id hprep
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hG, -⟩ := id hpack
  have hA := (hCp (ends e).1).image (hG (ends e).1)
  apply section34_piercing_components_after_first_trace_deletion hprep hpack e
    (hA.isCompact.image φ.continuous).isClosed ?_ ?_ hne.1 hne.2
  · rw [← φ.image_frontier, ← hA.boundary_eq_frontier]
    exact htrace
  · intro z _ hzT
    constructor
    · rintro ⟨y, hy, hyz⟩
      exact φ.injective (hyz.trans (hfix hzT).symm) ▸ hy
    · exact fun hz => ⟨z, hz, hfix hzT⟩

end DifferentialGeometry.Topology.PiecewiseLinear
