import DifferentialGeometry.Geometry.Comparison.Soul.SbrGradient
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.MetricSpace.IsometricSMul

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

@[simp] theorem intrinsicRightDerivative_add_const
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    (F : M → ℝ) (p : M) (v : TangentSpace I p) (c : ℝ) :
    intrinsicRightDerivative g hEnorm (fun q => F q + c) p v =
      intrinsicRightDerivative g hEnorm F p v := by
  change derivWithin (fun t => F (intrinsicGeodesic g hEnorm p v t) + c) (Ioi 0) 0 =
    derivWithin (fun t => F (intrinsicGeodesic g hEnorm p v t)) (Ioi 0) 0
  exact derivWithin_add_const c

variable [T2Space (TangentBundle I M)]

@[simp] theorem intrinsicGeneralizedGradient_add_const
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (c : ℝ) (p : M) :
    intrinsicGeneralizedGradient g hEnorm
        ((Isometry.lipschitzWith_iff L (isometry_add_right c)).mpr hF)
        (fun q u => (hconc q u).add_const c) p =
      intrinsicGeneralizedGradient g hEnorm hF hconc p := by
  have hFshift : LipschitzWith L (fun q => F q + c) :=
    (Isometry.lipschitzWith_iff L (isometry_add_right c)).mpr hF
  have hconcshift : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm q u t) + c) :=
    fun q u => (hconc q u).add_const c
  apply (intrinsicGeneralizedGradient_eq_iff g hEnorm hF hconc p _).mpr
  have hspec := intrinsicGeneralizedGradient_spec g hEnorm hFshift hconcshift p
  constructor
  · intro v
    simpa only [intrinsicRightDerivative_add_const] using hspec.1 v
  · simpa only [intrinsicRightDerivative_add_const] using hspec.2

theorem normalized_intrinsicGeneralizedGradient_add_const
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F)
    (hconc : ∀ (q : M) (u : TangentSpace I q),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm q u t)))
    (c : ℝ) (p : M) :
    let Gc := intrinsicGeneralizedGradient g hEnorm
      ((Isometry.lipschitzWith_iff L (isometry_add_right c)).mpr hF)
      (fun q u => (hconc q u).add_const c) p
    let G := intrinsicGeneralizedGradient g hEnorm hF hconc p
    (g.inner p Gc Gc)⁻¹ • Gc = (g.inner p G G)⁻¹ • G := by
  dsimp only
  rw [intrinsicGeneralizedGradient_add_const g hEnorm hF hconc c p]

end DifferentialGeometry.Geometry.Topology
