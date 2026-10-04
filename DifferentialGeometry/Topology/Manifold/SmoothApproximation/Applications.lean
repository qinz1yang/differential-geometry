import DifferentialGeometry.Topology.Manifold.SmoothApproximation.SmoothDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Consumers of W1 and W2

* `exists_smooth_diffeomorph_chart_close`: the finite-atlas `ε`-form consumed by LFR04
  (W4-F7a, Addendum 1, items (A1) and (A2), boundaryless case): a `C^k` diffeomorphism of compact
  boundaryless manifolds has, for any finite family of chart pieces and any `ε > 0`, a smooth
  diffeomorphism `Φ` mapping each piece into the same target chart and `ε`-close to it in every
  chart derivative of order `≤ k`.
* `nonempty_diffeomorph_sphere_of_diffeomorph`: a smooth manifold that is `C^k`-diffeomorphic
  (`1 ≤ k`) to the round sphere `Sⁿ ⊆ ℝⁿ⁺¹` is smoothly diffeomorphic to it.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold.SmoothApproximation

open DifferentialGeometry.CheegerGromovCompactness

section ChartClose

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {A : Type*} [TopologicalSpace A] [ChartedSpace H A] [IsManifold I ∞ A]
  [T2Space A] [CompactSpace A]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [J.Boundaryless]
  {B : Type*} [TopologicalSpace B] [ChartedSpace H' B] [IsManifold J ∞ B]

/-- **Finite-atlas `ε`-form (LFR04 (A1)+(A2), boundaryless case).** For a `C^k` diffeomorphism
`h` (`1 ≤ k`) of compact boundaryless manifolds, finitely many chart pieces `(p i, q i, K i)` with
`h (φ_{p i}⁻¹ (K i)) ⊆ source ψ_{q i}` and `ε > 0`, there is a smooth diffeomorphism `Φ` with
`Φ (φ_{p i}⁻¹ (K i)) ⊆ source ψ_{q i}` and all chart derivatives of order `≤ k` of
`ψ_{q i} ∘ Φ ∘ φ_{p i}⁻¹ - ψ_{q i} ∘ h ∘ φ_{p i}⁻¹` bounded by `ε` on `K i`. -/
theorem exists_smooth_diffeomorph_chart_close (k : ℕ) (hk : 1 ≤ k) (h : A ≃ₘ^k⟮I, J⟯ B)
    {ι : Type*} (s : Finset ι) (p : ι → A) (q : ι → B) (K : ι → Set E)
    (hK : ∀ i ∈ s, IsCompact (K i) ∧ K i ⊆ (extChartAt I (p i)).target ∧
      MapsTo (fun y => h ((extChartAt I (p i)).symm y)) (K i) (extChartAt J (q i)).source)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Φ : A ≃ₘ⟮I, J⟯ B, ∀ i ∈ s,
      MapsTo (fun y => Φ ((extChartAt I (p i)).symm y)) (K i) (extChartAt J (q i)).source ∧
      ∀ r ≤ k, ∀ y ∈ K i,
        mapDerivNorm r (fun y => extChartAt J (q i) (Φ ((extChartAt I (p i)).symm y)))
          (fun y => extChartAt J (q i) (h ((extChartAt I (p i)).symm y))) y ≤ ε := by
  obtain ⟨Φ, hΦ⟩ := exists_smooth_diffeomorph_seq_chart_tendsto k hk h
  have hev : ∀ i ∈ s, ∀ᶠ j in atTop,
      MapsTo (fun y => Φ j ((extChartAt I (p i)).symm y)) (K i) (extChartAt J (q i)).source ∧
      ∀ r ≤ k, ∀ y ∈ K i,
        mapDerivNorm r (fun y => extChartAt J (q i) (Φ j ((extChartAt I (p i)).symm y)))
          (fun y => extChartAt J (q i) (h ((extChartAt I (p i)).symm y))) y ≤ ε := by
    intro i hi
    obtain ⟨hKc, hKt, hKm⟩ := hK i hi
    obtain ⟨hmaps, hconv⟩ := hΦ (p i) (q i) (K i) hKc hKt hKm
    obtain ⟨j₀, hj₀⟩ := hconv ε hε
    filter_upwards [hmaps, eventually_ge_atTop j₀] with j hj hjj
    exact ⟨hj, fun r hr y hy => hj₀ j hjj r hr y hy⟩
  obtain ⟨j, hj⟩ := ((eventually_all_finset s).2 hev).exists
  exact ⟨Φ j, hj⟩

end ChartClose

section Sphere

/-- **Concrete consumer.** A smooth manifold `C^k`-diffeomorphic (`1 ≤ k`) to the round sphere
`Sⁿ ⊆ ℝⁿ⁺¹` is smoothly diffeomorphic to it. -/
theorem nonempty_diffeomorph_sphere_of_diffeomorph {n k : ℕ} (hk : 1 ≤ k)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (h : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₘ^k⟮𝓡 n, 𝓡 n⟯ M) :
    Nonempty (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ M) :=
  nonempty_diffeomorph_of_diffeomorph k hk h

end Sphere

end DifferentialGeometry.Topology.Manifold.SmoothApproximation
