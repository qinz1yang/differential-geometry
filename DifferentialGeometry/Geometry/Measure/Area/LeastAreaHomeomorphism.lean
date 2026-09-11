import DifferentialGeometry.Geometry.Measure.Area.WeakBoundaryCompetitors
import DifferentialGeometry.Topology.LoopSpace.HomeomorphismOrientation







noncomputable section

open Manifold DifferentialGeometry Function
open DifferentialGeometry.Topology
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T3Space M] [PreconnectedSpace M] [Nonempty M]




theorem leastSpanningArea_comp_weak_boundary (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ δ : lipschitzContractibleLoop g) (ψ : C(loopCircle, loopCircle))
    {f : ℝ → ℝ} (hc : Continuous f) (hm : Monotone f)
    (hp : ∀ t, f (t + 1) = f t + 1)
    (hlift : ∀ t : ℝ, ψ (t : loopCircle) = (f t : loopCircle))
    (htrace : δ.val.val = γ.val.val.comp ψ) :
    leastSpanningArea g δ = leastSpanningArea g γ := by
  have heq : ψ = affineCircleMap f hc hp := by
    ext θ
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective θ
    exact hlift t
  rw [heq] at htrace
  exact leastSpanningArea_comp_monotone_lift g γ δ hc hm hp htrace




theorem leastSpanningArea_comp_homeomorphism (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (γ δ : lipschitzContractibleLoop g) (ψ : loopCircle ≃ₜ loopCircle)
    (htrace : δ.val.val = γ.val.val.comp (⟨ψ, ψ.continuous⟩ : C(loopCircle, loopCircle))) :
    leastSpanningArea g δ = leastSpanningArea g γ := by
  rcases circleHomeomorph_affineLift_or_neg ψ with ⟨F, hp, hm, hψ⟩ | ⟨F, hp, hm, hψ⟩
  · apply leastSpanningArea_comp_monotone_lift g γ δ F.continuous hm.monotone hp
    rw [htrace]
    ext θ
    exact congrArg γ.val.val (hψ θ)
  · let R := Homeomorph.neg loopCircle
    have hR : LipschitzWith 1 R := by
      intro x y
      change edist (-x) (-y) ≤ (1 : ℝ≥0∞) * edist x y
      simp only [edist_neg_neg, one_mul, le_refl]
    have hR' : LipschitzWith 1 R.symm := hR
    let γr := precomposeLipschitzContractibleLoop g γ ⟨R, R.continuous⟩ hR
    have heq : leastSpanningArea g γr = leastSpanningArea g γ :=
      leastSpanningArea_precompose g γ R hR hR'
    rw [← heq]
    apply leastSpanningArea_comp_monotone_lift g γr δ F.continuous hm.monotone hp
    rw [htrace]
    ext θ
    change γ.val.val (ψ θ) = γ.val.val (-affineCircleMap F F.continuous hp θ)
    exact congrArg γ.val.val (hψ θ)

end DifferentialGeometry.Geometry
