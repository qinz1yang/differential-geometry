import Batteries.Tactic.Alias
import DifferentialGeometry.Geometry.Comparison.Soul.Defs
import DifferentialGeometry.Geometry.Submanifold.NormalBundle.Defs
import DifferentialGeometry.Geometry.Curvature.Nonnegative
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Basic

set_option autoImplicit false

open Bundle Manifold
open scoped ContDiff Manifold

namespace DifferentialGeometry.Geometry

def cheegerGromollSoulTheorem {E H M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : SmoothRiemannianMetric I M) : Prop :=
  ConnectedSpace M → NoncompactSpace M → BoundarylessManifold I M →
    RiemannianMetricComplete g → hasNonnegativeSectionalCurvature g →
    ∃ (S : Set M) (d : ℕ) (c : ChartedSpace (EuclideanSpace ℝ (Fin d)) S),
      letI := c
      let IS := 𝓘(ℝ, EuclideanSpace ℝ (Fin d))
      ∃ (m : IsManifold IS ∞ S),
        letI := m
        ∃ (gS : SmoothRiemannianMetric IS S)
          (soul : Soul gS g (Subtype.val : S → M)),
          let F := EuclideanSpace ℝ (Fin (Module.finrank ℝ E - d))
          let ν : S → Type _ := fun x ↦ soul.isometricImmersion.normalSpaceAt x
          ∃ (t : TopologicalSpace (TotalSpace F ν)),
            letI := t
            ∃ (b : FiberBundle F ν),
              letI := b
              ∃ (v : VectorBundle ℝ F ν),
                letI := v
                ContMDiffVectorBundle ∞ F ν IS ∧
                  IsSmoothEmbedding (IS.prod 𝓘(ℝ, F)) I.tangent ∞
                    (fun z : TotalSpace F ν ↦
                      (⟨(z.proj : M), z.snd.val⟩ : TangentBundle I M)) ∧
                  ∃ Phi : TotalSpace F ν ≃ₘ⟮IS.prod 𝓘(ℝ, F), I⟯ M,
                    ∀ x : S, Phi (Bundle.zeroSection F ν x) = (x : M)

end DifferentialGeometry.Geometry

namespace Poincare.Geometry

@[reducible] alias cheegerGromollSoulTheorem := DifferentialGeometry.Geometry.cheegerGromollSoulTheorem

end Poincare.Geometry
