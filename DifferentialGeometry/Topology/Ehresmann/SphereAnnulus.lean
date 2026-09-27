import DifferentialGeometry.Topology.Ehresmann.SphereProductData
import DifferentialGeometry.Topology.Ehresmann.SphereTube

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Ehresmann

open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Boundary DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Topology.SphereSeparation
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

section Conclusion

variable {E H W M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace W] [ChartedSpace H W]

def sphereAnnulusWithBoundaryMatching (ι : W → M) (e₀ e₁ : SphereTwo → M) : Prop :=
  ∃ u : W → ℝ, RegularIntervalDatum I u 0 1 ∧
    ι '' (u ⁻¹' {0}) = range e₀ ∧ ι '' (u ⁻¹' {1}) = range e₁ ∧
    ∃ Ψ : Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞,
    ∃ τ : Diffeomorph (𝓡 2) (𝓡 2) SphereTwo SphereTwo ∞,
      (∀ p, u (Ψ p) = (p.2 : ℝ)) ∧
      (∀ p, ι (Ψ (p, 0)) = e₀ p) ∧
      (∀ p, ι (Ψ (τ p, 1)) = e₁ p) ∧
      ((∃ Φ : Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞,
        (∀ p, ι (Φ (p, 0)) = e₀ p) ∧ (∀ p, ι (Φ (p, 1)) = e₁ p)) ↔
          sphereDiffeomorphDegree τ = 1) ∧
      (sphereDiffeomorphDegree τ = 1 →
        ∃ Φ : Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞,
          (∀ p, u (Φ p) = (p.2 : ℝ)) ∧
          (∀ p, ι (Φ (p, 0)) = e₀ p) ∧ (∀ p, ι (Φ (p, 1)) = e₁ p) ∧
          (∀ t : unitInterval, (t : ℝ) ≤ 1 / 3 → ∀ p, Φ (p, t) = Ψ (p, t)) ∧
          ∀ t : unitInterval, 2 / 3 ≤ (t : ℝ) → ∀ p, Φ (p, t) = Ψ (τ p, t))

end Conclusion

theorem sphereAnnulusWithBoundaryMatching_of_product
    {E H W M : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W]
    [hI : HasSmoothBoundary E H I] [IsManifold I ∞ W]
    [CompactSpace W] [PreconnectedSpace W]
    [TopologicalSpace M] [T2Space M] [ChartedSpace EuclideanThree M] [IsManifold (𝓡 3) ∞ M]
    (D : Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I (SphereTwo × unitInterval) W ∞)
    (ι : W → M) (hι : ContMDiff I (𝓡 3) ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I (𝓡 3) ι w))
    (hdim : Module.finrank ℝ E = 3)
    (e₀ e₁ : SphereTwo → M)
    (he₀ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₀)
    (he₁ : IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e₁)
    (hbdy : ι '' I.boundary W = range e₀ ∪ range e₁) :
    sphereAnnulusWithBoundaryMatching (I := I) ι e₀ e₁ := by
  let : T2Space W := hemb.t2Space
  obtain ⟨u, h, hfib₀, hfib₁, η₀, η₁, hη₀, hη₁⟩ :=
    exists_regular_height_of_labeled_sphere_product D ι hι hemb hinj hdim e₀ e₁ he₀ he₁ hbdy
  have ha : (0 : ℝ) ∈ range u := by rw [h.range_eq]; exact ⟨le_rfl, zero_le_one⟩
  have hb : (1 : ℝ) ∈ range u := by rw [h.range_eq]; exact ⟨zero_le_one, le_rfl⟩
  obtain ⟨Θ, hh, hl, P, hP, _⟩ := exists_boundary_endpoint_transport
    zero_lt_one h.smooth h.noncritical h.boundary_values ha hb
  let Ψ := unitCylinderDiffeomorphOfProduct 0 1 η₀ Θ
  let τ := η₁.trans (η₀.trans P).symm
  have hτ (p : SphereTwo) : η₀ (τ p) = P.symm (η₁ p) := by
    change η₀ (η₀.symm (P.symm (η₁ p))) = _
    exact η₀.apply_symm_apply _
  have hheight (p : SphereTwo × unitInterval) : u (Ψ p) = (p.2 : ℝ) := by
    rw [unitCylinderDiffeomorphOfProduct_apply, hh, affineIntervalDiffeomorph_apply]
    simp
  have hlow (p : SphereTwo) : ι (Ψ (p, 0)) = e₀ p := by
    exact (congrArg ι ((unitCylinderDiffeomorphOfProduct_lower 0 1 η₀ Θ p).trans
      (hl (η₀ p)))).trans (hη₀ p)
  have hupp (p : SphereTwo) : ι (Ψ (τ p, 1)) = e₁ p := by
    have he : Ψ (τ p, 1) = (η₁ p).1.1 := by
      calc
        Ψ (τ p, 1) = Θ (η₀ (τ p), ⟨1, zero_le_one, le_rfl⟩) :=
          unitCylinderDiffeomorphOfProduct_upper 0 1 η₀ Θ (τ p)
        _ = (P (η₀ (τ p))).1.1 := (hP (η₀ (τ p))).symm
        _ = (η₁ p).1.1 := by rw [hτ, P.apply_symm_apply]
    exact (congrArg ι he).trans (hη₁ p)
  have hiff := prescribed_sphere_boundary_matching_iff_degree_one zero_lt_one h.smooth.continuous
    h.boundary_values Θ P hh hl hP η₀ η₁
  refine ⟨u, h, hfib₀, hfib₁, Ψ, τ, hheight, hlow, hupp, ?_, ?_⟩
  · constructor
    · rintro ⟨Φ, h₀, h₁⟩
      apply hiff.mp
      exact ⟨Φ, fun p ↦ hemb.injective ((h₀ p).trans (hη₀ p).symm),
        fun p ↦ hemb.injective ((h₁ p).trans (hη₁ p).symm)⟩
    · intro ht
      obtain ⟨Φ, h₀, h₁⟩ := hiff.mpr ht
      exact ⟨Φ, fun p ↦ (congrArg ι (h₀ p)).trans (hη₀ p),
        fun p ↦ (congrArg ι (h₁ p)).trans (hη₁ p)⟩
  · intro ht
    obtain ⟨Φ, hΦ, h₀, h₁, hlo, hhi⟩ := exists_prescribed_sphere_boundary_matching_of_degree_one
      zero_lt_one h.smooth.continuous h.boundary_values Θ P hh hl hP η₀ η₁ ht
    refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
    · intro p
      simpa using hΦ p
    · intro p
      exact (congrArg ι (h₀ p)).trans (hη₀ p)
    · intro p
      exact (congrArg ι (h₁ p)).trans (hη₁ p)
    · intro t ht p
      rw [hlo t ht p, unitCylinderDiffeomorphOfProduct_apply]
    · intro t ht p
      rw [hhi t ht p, unitCylinderDiffeomorphOfProduct_apply, hτ]

end DifferentialGeometry.Topology.Ehresmann
