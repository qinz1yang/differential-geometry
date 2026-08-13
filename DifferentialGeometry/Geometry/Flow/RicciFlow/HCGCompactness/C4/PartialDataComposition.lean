import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PartialDataCompositionReverse

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open Bundle
open scoped Manifold ContDiff
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]

section PartialDataComp

open TopologicalSpace

theorem partialData_comp [I.Boundaryless] [NeZero (Module.finrank ℝ E)]
    {P : Type u} [TopologicalSpace P] [ChartedSpace H P] [IsManifold I ∞ P]
    [T2Space N] [SigmaCompactSpace N] [T2Space P] [SigmaCompactSpace P]
    [IsManifold I 1 M] [IsManifold I 2 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold I 1 N] [IsManifold I 2 N] [IsManifold I ((∞ : WithTop ℕ∞) + 1) N]
    [IsManifold I 1 P] [IsManifold I 2 P] [IsManifold I ((∞ : WithTop ℕ∞) + 1) P]
    (Φ : PartialDiffeomorph I I M N (∞ : WithTop ℕ∞))
    (Φ' : PartialDiffeomorph I I N P (∞ : WithTop ℕ∞))
    {U₁ : Opens M} [Nonempty U₁] (hU₁ : (U₁ : Set M) ⊆ Φ.source)
    {K₂ : Opens N} [Nonempty K₂] (hK₂ : (K₂ : Set N) ⊆ Φ'.source)
    (himg : (Φ : M → N) '' (U₁ : Set M) ⊆ (K₂ : Set N))
    {K : Set M} (hK : IsCompact K) (hKU : K ⊆ (U₁ : Set M))
    {ε ε' : ℝ} {p : ℕ} (hε2 : ε ≤ 1 / 2) (hε'2 : ε' ≤ 1 / 2)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ {M' : Type u} [TopologicalSpace M'] [ChartedSpace H M']
      [T2Space M'] [IsManifold I ∞ M'] [SigmaCompactSpace M']
      [IsManifold I 1 M'] [IsManifold I 2 M']
      [IsManifold I ((∞ : WithTop ℕ∞) + 1) M']
      {u : Set M'}, IsOpen u →
      ∀ (g₀ g₁ : SmoothRiemannianMetric I M')
        (δ₀ δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
          (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2)
        (eps0 eps1 : Real), 0 ≤ eps0 → eps0 ≤ 1 → 0 ≤ eps1 →
        (∀ x ∈ u, ∀ v : TangentSpace I x,
          (1 + eps0)⁻¹ * g₁.inner x v v ≤ g₀.inner x v v ∧
            g₀.inner x v v ≤ (1 + eps0) * g₁.inner x v v) →
        (∀ x ∈ u, ∀ j, 1 ≤ j → j ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + j)
            (iterCov (I := I) g₁ 2
              (Tensor0SBundle.metricTensorField (I := I) g₀) j x)) ≤ eps0) →
        (∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 δ₀ r x)) ≤ eps0) →
        (∀ x ∈ u, ∀ k, k ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₁ x (2 + k)
            (iterCov (I := I) g₁ 2 δ₁ k x)) ≤ eps1) →
        ∀ x ∈ u, ∀ r, 0 < r → r ≤ p →
          Real.sqrt (Tensor0SBundle.normSq0S (I := I) g₀ x (2 + r)
            (iterCov (I := I) g₀ 2 (δ₀ + δ₁) r x)) ≤ eps0 + eps1 * C)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (h' : SmoothRiemannianMetric I P)
    (D₁ : BookApproxIsoPartialData (I := I) (U₁ : Set M) ε p Φ g h)
    (D₂ : BookApproxIsoPartialData (I := I) (K₂ : Set N) ε' p Φ' h h') :
    ∀ ε'' : ℝ,
      ε / (1 - ε) + ε' * max C 2 ≤ ε'' →
      ε' / (1 - ε') + ε * max C 2 ≤ ε'' →
      ε'' < 1 →
      Nonempty (BookApproxIsoPartialData (I := I) K ε'' p
        (PartialDiffeomorph.trans (I := I) Φ Φ') g h') := by
  intro ε'' hlb1 hlb2 hub
  obtain ⟨Dforward⟩ := partialData_comp_forward (I := I) Φ Φ' hU₁ hK₂ himg
    hK hKU hε2 C hC0 hC g h h' D₁ D₂ ε'' hlb1 hub
  obtain ⟨Dreverse⟩ := partialData_comp_reverse (I := I) Φ Φ' hU₁ hK₂ himg
    hK hKU hε'2 C hC0 hC g h h' D₁ D₂ ε'' hlb2 hub
  have hsource : K ⊆ (PartialDiffeomorph.trans (I := I) Φ Φ').source := by
    intro y hy
    exact ⟨hU₁ (hKU hy), hK₂ (himg (Set.mem_image_of_mem _ (hKU hy)))⟩
  exact ⟨⟨hsource, Dforward, Dreverse⟩⟩

end PartialDataComp

end HCGCompactness
end DifferentialGeometry
