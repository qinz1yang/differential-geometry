import DifferentialGeometry.Geometry.Comparison.Variation.Flow
import DifferentialGeometry.Geometry.Metric.DeTurck.VectorField

open DifferentialGeometry.Geometry.Connection

noncomputable section

open Set Bundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.PDE.DeTurck
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [BoundarylessManifold I M]
      [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [SigmaCompactSpace M] in
theorem flow_cov_variation
    (g : SmoothRiemannianMetric I M)
    (X : ℝ → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, ℝ)) t).toContinuousLinearMap.smulRight
            (-(X t ((Φ_fam t : M → M) x)))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v : TangentSpace I x) :
    covDerivAlong (I := I) g (fun s : ℝ => (Φ_fam s : M → M) x)
        (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x v) t =
      -((LeviCivita (I := I) g) (X t : ∀ y : M, TangentSpace I y)
        ((Φ_fam t : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v)) := by
  exact DifferentialGeometry.Geometry.Riemannian.Variation.flow_cov_variation
    (I := I) g X T Φ_fam hΦode hjoint t ht x v

omit [NeZero (Module.finrank ℝ E)]
  [CompactSpace M] [SigmaCompactSpace M] in
theorem conjugating_flow_covariant_variational_eq
    (g_DT : ℝ → SmoothRiemannianMetric I M) (g_bg : SmoothRiemannianMetric I M)
    (T : ℝ) (Φ_fam : ℝ → (M ≃ₘ⟮I, I⟯ M))
    (hΦode : ∀ x : M, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun s : ℝ => (Φ_fam s : M → M) x)
        (Set.Ici (0 : ℝ)) t
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, ℝ)) t).toContinuousLinearMap.smulRight
            (-(deTurckVF (I := I) (g_DT t) g_bg ((Φ_fam t : M → M) x)))))
    (hjoint : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞
      (fun q : ℝ × M => (Φ_fam q.1 : M → M) q.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Set.univ))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T) (x : M) (v : TangentSpace I x) :
    covDerivAlong (I := I) (g_DT t) (fun s : ℝ => (Φ_fam s : M → M) x)
        (fun s : ℝ => mfderiv I I (Φ_fam s : M → M) x v) t =
      -((LeviCivita (I := I) (g_DT t))
        (fun y : M => deTurckVF (I := I) (g_DT t) g_bg y)
        ((Φ_fam t : M → M) x)
        (mfderiv I I (Φ_fam t : M → M) x v)) := by
  exact DifferentialGeometry.Geometry.Riemannian.Variation.flow_cov_variation
    (I := I) (g_DT t) (fun s => deTurckVF (I := I) (g_DT s) g_bg)
    T Φ_fam hΦode hjoint t ht x v

end DifferentialGeometry.PDE.RicciFlow

end
