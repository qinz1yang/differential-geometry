import DifferentialGeometry.Topology.Morse.BoundaryExcellentDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Filter Function Bundle
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
namespace Poincare.Morse
variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
  [T2Space M] [CompactSpace M]


theorem exists_relative_excellent_morse_sublevel_homeomorph (b : ℝ) :
    ∃ (f : M → ℝ) (a c₀ : ℝ) (W : TopologicalSpace.Opens M),
      ContMDiff (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) ∞ f ∧ a < c₀ ∧ c₀ < b ∧
      (∀ x, a < f x ∧ f x ≤ b) ∧ f ⁻¹' Iic a = ∅ ∧ f ⁻¹' {b} = (𝓡∂ (n + 1)).boundary M ∧
      (𝓡∂ (n + 1)).boundary M ⊆ W ∧ f ⁻¹' Icc c₀ b ⊆ W ∧
      (∀ x, IsCriticalPointAt (𝓡∂ (n + 1)) f x →
        (𝓡∂ (n + 1)).IsInteriorPoint x ∧ IsNondegenerateCriticalPointAt (𝓡∂ (n + 1)) f x ∧ f x < c₀) ∧
      (∀ x, f x = c₀ → ¬ IsCriticalPointAt (𝓡∂ (n + 1)) f x) ∧
      {x : M | IsCriticalPointAt (𝓡∂ (n + 1)) f x}.Finite ∧
      InjOn f {x | IsCriticalPointAt (𝓡∂ (n + 1)) f x} ∧
      (∀ x, f x ≤ c₀ → (𝓡∂ (n + 1)).IsInteriorPoint x) ∧
      Nonempty (M ≃ₜ SublevelSpace f c₀) ∧
      ∃ V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y,
        ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞ (fun y => (⟨y,V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)) ∧
        IsCompact (tsupport V) ∧
        (∀ y ∈ W, (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, ℝ) f y) (V y) = (-1 : ℝ)) ∧
        ∀ y : BoundaryManifold (𝓡∂ (n + 1)) M,
          0 < (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n + 1))) (V y) := by
  obtain ⟨f, a, t, c₀, W, hf, hreg, hi, d, hat, htc, hcb, hbound, hempty,
    hlevel, hBW, hband, hcrit, hfinite, hinj, _, _, _, V, hV, hVc, hunit, hVpos⟩ :=
    exists_relative_excellent_morse_sublevel_diffeomorph (M := M) (n := n) b
  let _ := Poincare.Manifold.RegularLevel.interiorSublevelChartedSpace (𝓡∂ (n + 1))
    (EuclideanSpace.equiv (Fin (n + 1)) ℝ) hf hreg hi
  refine ⟨f, a, c₀, W, hf, hat.trans htc, hcb, hbound, hempty, hlevel, hBW, hband,
    ?_, hreg, hfinite, hinj, (fun x hx => hi hx), ⟨d.toHomeomorph⟩, V, hV, hVc, hunit, hVpos⟩
  intro x hx
  exact ⟨(hcrit x hx).1, (hcrit x hx).2.1, (hcrit x hx).2.2.trans htc⟩

end Poincare.Morse
