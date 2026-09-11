import DifferentialGeometry.Topology.Manifold.BoundaryCollar.ManifoldLocalFlow
import DifferentialGeometry.Topology.Manifold.BoundaryCollar.InwardField

open Set Function Topology Manifold
open scoped ContDiff
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.Manifold.BoundaryCollar

theorem exists_smooth_boundary_localFlows
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    ∃ V : (y : M) → TangentSpace (𝓡∂ (n + 1)) y,
      ContMDiff (𝓡∂ (n + 1)) (𝓡∂ (n + 1)).tangent ∞
        (fun y => (⟨y, V y⟩ : TangentBundle (𝓡∂ (n + 1)) M)) ∧
      IsCompact (tsupport V) ∧
      ∀ p : BoundaryManifold (𝓡∂ (n + 1)) M,
        ∃ O : TopologicalSpace.Opens M, (p : M) ∈ O ∧
          ∃ ε : ℝ, 0 < ε ∧ ∃ Φ : M × ℝ → M,
            ContMDiffOn ((𝓡∂ (n + 1)).prod 𝓘(ℝ, ℝ)) (𝓡∂ (n + 1)) ∞ Φ
              ((O : Set M) ×ˢ Icc (0 : ℝ) ε) ∧
            Φ ((p : M), 0) = boundaryInclusion (𝓡∂ (n + 1)) M p ∧
            (∀ y ∈ O, Φ (y, 0) = y) ∧
            (∀ y ∈ O, IsMIntegralCurveOn (fun t => Φ (y, t)) V (Icc (0 : ℝ) ε)) ∧
            (∀ y ∈ O, ∀ t ∈ Ioc (0 : ℝ) ε,
              (𝓡∂ (n + 1)).IsInteriorPoint (Φ (y, t))) ∧
            (∀ t ∈ Icc (0 : ℝ) ε, InjOn (fun y => Φ (y, t)) O) ∧
            ∀ y ∈ O, ∀ s ∈ Icc (0 : ℝ) ε, ∀ t : ℝ,
              Φ (Φ (y, s), t) = Φ (y, s + t) := by
  obtain ⟨V, hV, hVK, hnormal⟩ := exists_smooth_inwardField hK
  refine ⟨V, hV, hVK, ?_⟩
  intro p
  obtain ⟨O, hpO, ε, hε, Φ, hΦ, hzero, hcurve, hi, hinj, hadd⟩ :=
    exists_inward_manifold_localFlow p.2 hV (hnormal p).1
  exact ⟨O, hpO, ε, hε, Φ, hΦ, hzero p hpO, hzero, hcurve, hi, hinj, hadd⟩

end DifferentialGeometry.Manifold.BoundaryCollar
