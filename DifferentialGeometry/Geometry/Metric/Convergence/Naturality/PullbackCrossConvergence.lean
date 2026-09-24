import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]
  [T2Space N]

private local instance crossMetricConvergenceSourceC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance crossMetricConvergenceSourceC2 : IsManifold I 2 M :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance crossMetricConvergenceSourceTop :
    IsManifold I ((∞ : WithTop ℕ∞) + 1) M := by
  simpa using (inferInstance : IsManifold I ∞ M)

private local instance crossMetricConvergenceTargetC1 : IsManifold J 1 N :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance crossMetricConvergenceTargetC2 : IsManifold J 2 N :=
  IsManifold.of_le (n := ∞) (by decide)

private local instance crossMetricConvergenceTargetTop :
    IsManifold J ((∞ : WithTop ℕ∞) + 1) N := by
  simpa using (inferInstance : IsManifold J ∞ N)

theorem metricDerivNormSupOn_pullbackCross_image
    (K : Set M) (p : ℕ) (gk gInf gRef : SmoothRiemannianMetric J N)
    (Phi : M ≃ₘ⟮I, J⟯ N) :
    metricDerivNormSupOn (I := I) K p
        (Diffeomorph.pullbackMetricCross gk Phi)
        (Diffeomorph.pullbackMetricCross gInf Phi)
        (Diffeomorph.pullbackMetricCross gRef Phi) =
      metricDerivNormSupOn (I := J) (Phi '' K) p gk gInf gRef := by
  unfold metricDerivNormSupOn
  apply congrArg sSup
  ext r
  constructor
  · rintro ⟨a, ha, x, hx, hr⟩
    refine ⟨a, ha, Phi x, ⟨x, hx, rfl⟩, ?_⟩
    rw [← hr]
    exact (metricDerivNorm_pullbackCross (I := I) (J := J)
      gk gInf gRef Phi a x).symm
  · rintro ⟨a, ha, y, ⟨x, hx, rfl⟩, hr⟩
    refine ⟨a, ha, x, hx, ?_⟩
    rw [metricDerivNorm_pullbackCross (I := I) (J := J)]
    exact hr

theorem metricCPConvOn_pullbackCross
    (K : Set M) (p : ℕ) (gSeq : ℕ → SmoothRiemannianMetric J N)
    (gInf gRef : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (hconv : MetricCPConvergenceOn (I := J) (Phi '' K) p gSeq gInf gRef) :
    MetricCPConvergenceOn (I := I) K p
      (fun k => Diffeomorph.pullbackMetricCross (gSeq k) Phi)
      (Diffeomorph.pullbackMetricCross gInf Phi)
      (Diffeomorph.pullbackMetricCross gRef Phi) := by
  intro ε hε
  obtain ⟨k₀, hk₀⟩ := hconv ε hε
  refine ⟨k₀, fun k hk => ?_⟩
  rw [metricDerivNormSupOn_pullbackCross_image]
  exact hk₀ k hk

theorem metricCInfConvOnCompacts_pullbackCross
    (gSeq : ℕ → SmoothRiemannianMetric J N)
    (gInf gRef : SmoothRiemannianMetric J N) (Phi : M ≃ₘ⟮I, J⟯ N)
    (hconv : MetricCInfConvergenceOnCompacts (I := J) gSeq gInf gRef) :
    MetricCInfConvergenceOnCompacts (I := I)
      (fun k => Diffeomorph.pullbackMetricCross (gSeq k) Phi)
      (Diffeomorph.pullbackMetricCross gInf Phi)
      (Diffeomorph.pullbackMetricCross gRef Phi) := by
  intro K hK p
  exact metricCPConvOn_pullbackCross K p gSeq gInf gRef Phi
    (hconv (Phi '' K) (hK.image Phi.continuous) p)

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
