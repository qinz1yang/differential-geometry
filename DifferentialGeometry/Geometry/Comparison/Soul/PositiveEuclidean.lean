import DifferentialGeometry.Geometry.Comparison.Soul.PositiveSoulDiffeomorph
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M] [NoncompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

theorem eq_singleton_of_positiveSectionalCurvature
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : Poincare.Geometry.HasPositiveSectionalCurvature (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {S : Set M} (hne : S.Nonempty) (hcompact : IsCompact S)
    (hconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) :
    ∃ p : M, S = {p} :=
  eq_singleton_of_maxSliceDim_eq_zero g hEnorm hconv hne hB
    (maxSliceDim_eq_zero_of_positiveSectionalCurvature g hEnorm hsec hdim
      hne hcompact hconv hB)

theorem exists_diffeomorph_euclidean_of_positiveSectionalCurvature
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : Poincare.Geometry.HasPositiveSectionalCurvature (I := I) g)
    {n : ℕ} (hdim : Module.finrank ℝ E = n) :
    ∃ p : M, ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯
        EuclideanSpace ℝ (Fin n), e p = 0 := by
  classical
  obtain ⟨p₀⟩ := (inferInstance : Nonempty M)
  obtain ⟨S, p, _hS, _hne, _hcompact, _hconv, _hB, _hzero, e, he⟩ :=
    exists_point_soul_diffeomorph g hEnorm hsec p₀
  let A : E ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.ofFinrankEq (by simpa only [finrank_euclideanSpace_fin] using hdim)
  refine ⟨p, e.trans A.toDiffeomorph, ?_⟩
  change A (e p) = 0
  rw [he, map_zero]

theorem exists_diffeomorph_euclidean_three_of_positiveSectionalCurvature
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : Poincare.Geometry.HasPositiveSectionalCurvature (I := I) g)
    (hdim : Module.finrank ℝ E = 3) :
    ∃ p : M, ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯
        EuclideanSpace ℝ (Fin 3), e p = 0 :=
  exists_diffeomorph_euclidean_of_positiveSectionalCurvature g hEnorm hsec hdim

end DifferentialGeometry.Geometry.Topology

end
