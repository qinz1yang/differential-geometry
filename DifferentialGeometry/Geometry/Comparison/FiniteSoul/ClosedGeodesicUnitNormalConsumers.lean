import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicUnitNormal
import DifferentialGeometry.Geometry.Comparison.FiniteSoul.ClosedGeodesicTubeConsumers

/-!
# Consumer of SA6: the circle tube without a prescribed normal field

`exists_unitNormal_and_closedGeodesic_tube_dim_two`: for a closed unit geodesic of a complete
finite surface (the circle output of S-SHAPE2 / S-SOUL2) a continuous unit normal field exists
(SA6), and lane CMS-T's frozen S-TUBE statement `exists_closedGeodesic_tube` applies to it.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Geometry.FiniteSoul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]
  [CompleteSpace M]

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {r : ℕ∞}

/-- **Consumer of SA6.** A closed unit geodesic of a complete finite surface carries a
continuous unit normal field `ν`, and the normal exponential `(t, h) ↦ exp_{γ t}(h ν t)` is
injective on `[0, ℓ) × (−ε, ε)`, maps onto `{d_S < ε}` and is calibrated (`d_S = |h|`). -/
theorem exists_unitNormal_and_closedGeodesic_tube_dim_two
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (hdim : Module.finrank ℝ E = 2) (p : TangentBundle I M) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hunit : g.inner p.proj p.snd p.snd = 1) (hper : g.geodesicFlow p ℓ = p)
    (hinj : InjOn (fun t => (g.geodesicFlow p t).proj) (Ico 0 ℓ)) :
    ∃ ν : ℝ → E,
      (Continuous (fun t => (⟨(g.geodesicFlow p t).proj, ν t⟩ : TangentBundle I M)) ∧
        (∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (ν t) = 1) ∧
        ∀ t, g.inner (g.geodesicFlow p t).proj (ν t) (g.geodesicFlow p t).snd = 0) ∧
      ∃ ε > 0,
        InjOn (fun z : ℝ × ℝ =>
            g.expMap (⟨(g.geodesicFlow p z.1).proj, z.2 • ν z.1⟩ : TangentBundle I M))
          (Ico 0 ℓ ×ˢ Ioo (-ε) ε) ∧
        (fun z : ℝ × ℝ =>
            g.expMap (⟨(g.geodesicFlow p z.1).proj, z.2 • ν z.1⟩ : TangentBundle I M)) ''
            (Ico 0 ℓ ×ˢ Ioo (-ε) ε) =
          {y | infDist y (range (fun t => (g.geodesicFlow p t).proj)) < ε} ∧
        ∀ z ∈ Ico 0 ℓ ×ˢ Ioo (-ε) ε,
          infDist (g.expMap (⟨(g.geodesicFlow p z.1).proj, z.2 • ν z.1⟩ : TangentBundle I M))
            (range (fun t => (g.geodesicFlow p t).proj)) = |z.2| := by
  obtain ⟨ν, hνc, hνu, hνp⟩ :=
    exists_unitNormal_closedGeodesic_dim_two g hr hnorm hdim p hℓ hunit hper
  exact ⟨ν, ⟨hνc, hνu, hνp⟩,
    exists_closedGeodesic_tube g hr hnorm hdim p hℓ hunit hper hinj ν hνc hνu hνp⟩

end DifferentialGeometry.Geometry.FiniteSoul
