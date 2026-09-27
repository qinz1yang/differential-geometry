import DifferentialGeometry.Topology.SphereSeparation.FlatCapBallReconstruction

open Set Metric Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.SphereSeparation

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

theorem exists_diffeomorph_ball_of_cylinderCap_replacements
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {b : Fin 2 → ClosedCell 2 → SphereTwo}
    (hb : ∀ i, IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (b i))
    {η : AddCircle (1 : ℝ) → SphereTwo}
    (hbboundary : ∀ i, range (b i ∘ cellBoundaryInclusion 2) = range η)
    (hcover : range (b 0) ∪ range (b 1) = univ)
    (hinter : range (b 0) ∩ range (b 1) = range η)
    (Ψ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] EuclideanThree)
    {R ε : ℝ} (hR : 1 < R)
    (hS : Ψ ⁻¹' range e ∩ (closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Icc (-ε) ε) =
      sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ Icc (-ε) ε)
    (hboundary : e '' range η = Ψ '' (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (χ : Fin 2 → PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞)
    (hχ : ∀ i, closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ (χ i).source)
    (hχD : ∀ i, χ i '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = range (b i))
    {a : Fin 2 → ℝ} {σ : ℝ} (ha : ∀ i, 0 < a i) (haε : ∀ i, a i < ε)
    (hσ : σ = 1 ∨ σ = -1)
    {f : Fin 2 → SphereTwo → EuclideanThree}
    (hf : ∀ i, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i))
    (hcap : ∀ i, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap ((if i = 0 then σ else -σ) * a i) x))
    (hffix : ∀ i, EqOn (f i) e (range (b i))ᶜ)
    (hret : ∀ i, ∀ p ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Ioo (-ε) ε,
      Ψ p ∈ e '' (range (b i))ᶜ ↔ ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2)
    (D : Fin 2 → EuclideanThree ≃ₘ[ℝ] EuclideanThree)
    (hD : ∀ i, D i '' closedBall 0 1 = closure
      (jordanBrouwer_openThreeSpace (f i) (hf i)
        (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides.compactSide) :
    let d := (jordanBrouwer_openThreeSpace e he
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    ∃ H : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
      H '' closedBall 0 1 = closure d.compactSide ∧ H '' sphere 0 1 = range e := by
  have hε : 0 < ε := (ha 0).trans (haε 0)
  have hinter' : e '' (range (b 0) ∩ range (b 1)) ⊆
      Ψ '' (closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}) := by
    rw [hinter, hboundary]
    exact image_mono (prod_mono sphere_subset_closedBall (Subset.refl _))
  obtain ⟨g, hg, hgin, hgun⟩ := he.isEmbedding.exists_two_flat_cap_replacements
    Ψ.toHomeomorph.isEmbedding (fun i => (χ i).toOpenPartialHomeomorph) hR hε
    hcover hinter' hχ hχD (fun i => (hf i).contMDiff.continuous) hcap hffix hret
  exact exists_diffeomorph_ball_of_flat_cap_reconstruction he hb hbboundary hcover hinter Ψ hR hS
    hboundary χ hχ hχD ha haε hσ hf hcap hffix hret (fun i => (hg i).2.1)
    (fun i => (hg i).2.2.1) (fun i => (hg i).2.2.2.1) hgin hgun D hD

theorem exists_diffeomorph_ball_of_cylinderCap_images
    {e : SphereTwo → EuclideanThree} (he : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    {b : Fin 2 → ClosedCell 2 → SphereTwo}
    (hb : ∀ i, IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ (b i))
    {η : AddCircle (1 : ℝ) → SphereTwo}
    (hbboundary : ∀ i, range (b i ∘ cellBoundaryInclusion 2) = range η)
    (hcover : range (b 0) ∪ range (b 1) = univ)
    (hinter : range (b 0) ∩ range (b 1) = range η)
    (Ψ : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₘ[ℝ] EuclideanThree)
    {R ε : ℝ} (hR : 1 < R)
    (hS : Ψ ⁻¹' range e ∩ (closedBall (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Icc (-ε) ε) =
      sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ Icc (-ε) ε)
    (hboundary : e '' range η = Ψ '' (sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ×ˢ {0}))
    (χ : Fin 2 → PartialDiffeomorph (𝓡 2) (𝓡 2) (EuclideanSpace ℝ (Fin 2)) SphereTwo ∞)
    (hχ : ∀ i, closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ⊆ (χ i).source)
    (hχD : ∀ i, χ i '' closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = range (b i))
    {a : Fin 2 → ℝ} {σ : ℝ} (ha : ∀ i, 0 < a i) (haε : ∀ i, a i < ε)
    (hσ : σ = 1 ∨ σ = -1)
    {f : Fin 2 → SphereTwo → EuclideanThree}
    (hf : ∀ i, IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (f i))
    (hcap : ∀ i, ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
      f i (χ i x) = Ψ (EuclideanGeometry.cylinderCap ((if i = 0 then σ else -σ) * a i) x))
    (hffix : ∀ i, EqOn (f i) e (range (b i))ᶜ)
    (hret : ∀ i, ∀ p ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) R ×ˢ Ioo (-ε) ε,
      Ψ p ∈ e '' (range (b i))ᶜ ↔ ‖p.1‖ = 1 ∧ 0 < (if i = 0 then σ else -σ) * p.2)
    (T D : Fin 2 → EuclideanThree ≃ₘ[ℝ] EuclideanThree)
    (hD : ∀ i, D i '' sphere 0 1 = range (T i ∘ f i)) :
    let d := (jordanBrouwer_openThreeSpace e he
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    ∃ H : EuclideanThree ≃ₘ[ℝ] EuclideanThree,
      H '' closedBall 0 1 = closure d.compactSide ∧ H '' sphere 0 1 = range e := by
  let A : Fin 2 → EuclideanThree ≃ₘ[ℝ] EuclideanThree := fun i => (D i).trans (T i).symm
  have hAsphere (i : Fin 2) : A i '' sphere 0 1 = range (f i) := by
    change ((T i).symm ∘ D i) '' _ = _
    rw [image_comp, hD i, range_comp]
    exact (T i).symm_image_image _
  have hAball (i : Fin 2) : A i '' closedBall 0 1 = closure
      (jordanBrouwer_openThreeSpace (f i) (hf i)
        (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides.compactSide := by
    let d := (jordanBrouwer_openThreeSpace (f i) (hf i)
      (Diffeomorph.refl (𝓡 3) EuclideanThree ∞)).toSphereSides
    let d' := standardUnitSphereSides.image (A i).toHomeomorph
    have hunion : d'.compactSide ∪ d'.endSide = (range (f i))ᶜ := by
      rw [d'.union_eq_compl]
      change (A i '' sphere 0 1)ᶜ = _
      rw [hAsphere i]
    have hside := (d.side_sets_unique_of_core_properties d'.compactSide d'.endSide
      d'.isOpen_compactSide d'.isOpen_endSide d'.isConnected_compactSide d'.isConnected_endSide
      d'.disjoint hunion d'.isCompact_closure_compactSide d'.not_isCompact_closure_endSide).1
    change A i '' ball 0 1 = d.compactSide at hside
    have hclosure : A i '' closure (ball 0 1) = closure (A i '' ball 0 1) :=
      (A i).toHomeomorph.image_closure _
    rw [closure_ball _ one_ne_zero, hside] at hclosure
    exact hclosure
  exact exists_diffeomorph_ball_of_cylinderCap_replacements he hb hbboundary hcover hinter Ψ hR hS hboundary
    χ hχ hχD ha haε hσ hf hcap hffix hret A hAball

end DifferentialGeometry.Topology.SphereSeparation
