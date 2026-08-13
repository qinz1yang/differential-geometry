import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.ApproxIsoSeparationReverse

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

set_option backward.isDefEq.respectTransparency false in
noncomputable def sepData_comp [I.Boundaryless] [NeZero (Module.finrank Real E)]
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
    {c0 cov c0' cov' qF eF qR eR c0'' cov'' : Real} {p : Nat}
    (hc0_half : c0 ≤ 1 / 2) (hc0'_half : c0' ≤ 1 / 2)
    (hqF0 : 0 ≤ qF) (hqF1 : qF ≤ 1)
    (hqF_c0 : c0 / (1 - c0) ≤ qF) (hqF_cov : cov ≤ qF)
    (heF0 : 0 ≤ eF) (heF_c0 : c0' ≤ eF) (heF_cov : cov' ≤ eF)
    (hqR0 : 0 ≤ qR) (hqR1 : qR ≤ 1)
    (hqR_c0 : c0' / (1 - c0') ≤ qR) (hqR_cov : cov' ≤ qR)
    (heR0 : 0 ≤ eR) (heR_c0 : c0 ≤ eR) (heR_cov : cov ≤ eR)
    (C : Real) (hC0 : 0 ≤ C)
    (hc0F_out : c0 + c0' * (1 + qF) ≤ c0'')
    (hcovF_out : qF + eF * C ≤ cov'')
    (hc0R_out : c0' + c0 * (1 + qR) ≤ c0'')
    (hcovR_out : qR + eR * C ≤ cov'')
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
            (iterCov (I := I) g₀ 2
              (δ₀ + δ₁ : Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
                (I := I) (M := M') (n := (∞ : WithTop ℕ∞)) 2) r x)) ≤ eps0 + eps1 * C)
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (h' : SmoothRiemannianMetric I P)
    (D₁ : BookApproxIsoSep (I := I) (U₁ : Set M) c0 cov p Φ g h)
    (D₂ : BookApproxIsoSep (I := I) (K₂ : Set N) c0' cov' p Φ' h h') :
    BookApproxIsoSep (I := I) K c0'' cov'' p
      (PartialDiffeomorph.trans (I := I) Φ Φ') g h' where
  source_sub := by
    intro y hy
    exact ⟨hU₁ (hKU hy), hK₂ (himg (Set.mem_image_of_mem _ (hKU hy)))⟩
  forward := compSepFwd (I := I) Φ Φ' hU₁ hK₂ himg hK hKU hc0_half
    hqF0 hqF1 hqF_c0 hqF_cov heF0 heF_c0 heF_cov C hC0 hc0F_out hcovF_out hC
    g h h' D₁ D₂
  reverse := compSepRev (I := I) Φ Φ' hU₁ hK₂ himg hK hKU hc0'_half
    hqR0 hqR1 hqR_c0 hqR_cov heR0 heR_c0 heR_cov C hC0 hc0R_out hcovR_out hC
    g h h' D₁ D₂

end PartialDataComp

end HCGCompactness
end DifferentialGeometry
