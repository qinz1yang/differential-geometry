import DifferentialGeometry.Analysis.Calculus.Derivative.TargetModulus
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.StaticWitness

set_option autoImplicit false
noncomputable section
open Set Filter Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Neck DifferentialGeometry.Analysis
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
universe u v w

theorem exists_staticInsertion_modulus :
    ∃ (A : ℝ) (hA : 0 < A), 2 * A < 1 / 2 ∧ ∀ m : ℕ,
      ∃ δₘ : ℝ, 0 < δₘ ∧ ∃ modulus : ℝ → ℝ,
        MapsTo modulus (Ioc 0 δₘ) (Ioc 0 1) ∧ Tendsto modulus (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δₘ →
        ∀ {E : Type u} {H : Type v} {M : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
          [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
          [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
          [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
          ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ (m + 4)),
            Nonempty (CanonicalStaticInsertionWitness d A hA (modulus δ)⁻¹ m (modulus δ)) := by
  obtain ⟨A, hA, hsmall, hmod⟩ := exists_canonicalStaticInsertionWitness.{u, v, w}
  refine ⟨A, hA, hsmall, ?_⟩
  intro m
  let P (δ : ℝ) (n : ℕ) : Prop :=
    ∀ {E : Type u} {H : Type v} {M : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = 3)]
      [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
      [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M],
      ∀ (g : SmoothRiemannianMetric I M) (x₀ : M) (d : normalizedDatum g x₀ δ (m + 4)),
        Nonempty (CanonicalStaticInsertionWitness d A hA ((n : ℝ) + 1) m (((n : ℝ) + 1)⁻¹))
  have hP : ∀ n : ℕ, ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ → δ ≤ η → P δ n := by
    intro n
    have hpos : 0 < (n : ℝ) + 1 := by positivity
    obtain ⟨η, hη, _, hb⟩ := hmod ((n : ℝ) + 1) hpos m (((n : ℝ) + 1)⁻¹) (inv_pos.mpr hpos)
    exact ⟨η, hη, hb⟩
  obtain ⟨δₘ, hδₘ, modulus, hmodulus, hlim, hw⟩ := exists_target_modulus P hP
  refine ⟨δₘ, hδₘ, modulus, hmodulus, hlim, ?_⟩
  intro δ hδ hle
  obtain ⟨n, hn, hp⟩ := hw δ hδ hle
  intro E H M _ _ _ _ _ I _ _ _ _ _ g x₀ d
  simpa only [hn, inv_inv] using hp g x₀ d
end DifferentialGeometry.PDE.RicciFlow.StandardCap
