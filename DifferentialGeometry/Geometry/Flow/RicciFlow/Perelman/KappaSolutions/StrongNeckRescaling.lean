import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StrongNeck
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CurvatureNormalization


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle _root_.Manifold Set
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

private local instance strongRescalingSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

private local instance strongRescalingC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

omit [T2Space M] in
theorem strongNeckNormalizedMetric_curvatureNormalizedSolution
    (S : SolutionOn (I := I) (M := M) D) (p : M) (t : ℝ)
    (ht : t ∈ D.carrier) (hQ : 0 < S.scalar t p)
    {epsilon : ℝ} {f : C(spatialNeckBuffer epsilon, M)}
    (hf : IsSmoothEmbedding SpatialNeckCylinderModel I ∞ f)
    (hR : 0 < (curvatureNormalizedSolution S t (S.scalar t p) hQ ht).scalar 0 p)
    (s : ℝ) :
    strongNeckNormalizedMetric (curvatureNormalizedSolution S t (S.scalar t p) hQ ht)
        p 0 hR hf s = strongNeckNormalizedMetric S p t hQ hf s := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [strongNeckNormalizedMetric_inner, strongNeckNormalizedMetric_inner,
    curvatureNormalizedSolution_scalar_base S t (S.scalar t p) hQ ht p rfl,
    zero_add, div_one, one_mul]
  change (scaleMetric (S.scalar t p) hQ (S.base.metric (parabolicTime t (S.scalar t p) s))).inner
      (f x) (mfderiv SpatialNeckCylinderModel I f x v) (mfderiv SpatialNeckCylinderModel I f x w) = _
  rw [scaleMetric_inner]
  rfl


def StrongNeckWitness.ofCurvatureNormalization
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcarrier : D.carrier = Iic (0 : ℝ))
    (yStar : SpatialNeckSphere) (p : M) (t : ℝ)
    (ht : t ∈ D.carrier) (hQ : 0 < S.scalar t p) {epsilon : ℝ}
    (W : StrongNeckWitness (curvatureNormalizedSolution S t (S.scalar t p) hQ ht)
      yStar p 0 epsilon) : StrongNeckWitness S yStar p t epsilon where
  dimension_three := W.dimension_three
  isSolution := hS
  epsilon_pos := W.epsilon_pos
  epsilon_lt_one := W.epsilon_lt_one
  scalar_pos := hQ
  time_window := by
    rw [hcarrier] at ht ⊢
    exact fun _ hs => hs.2.trans ht
  embedding := W.embedding
  smooth_embedding := W.smooth_embedding
  marked := W.marked
  jet := W.jet
  jet_zero := by
    intro s hs x v
    rw [W.jet_zero s hs x v,
      strongNeckNormalizedMetric_curvatureNormalizedSolution S p t ht hQ
        W.smooth_embedding W.scalar_pos s]
  jet_succ := W.jet_succ
  closeness := W.closeness


theorem isStrongNeckCenter_of_curvatureNormalizedSolution
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hcarrier : D.carrier = Iic (0 : ℝ))
    (yStar : SpatialNeckSphere) (p : M) (t : ℝ)
    (ht : t ∈ D.carrier) (hQ : 0 < S.scalar t p) {epsilon : ℝ}
    (hneck : IsStrongNeckCenter (curvatureNormalizedSolution S t (S.scalar t p) hQ ht)
      yStar p 0 epsilon) : IsStrongNeckCenter S yStar p t epsilon := by
  obtain ⟨W⟩ := hneck
  exact ⟨W.ofCurvatureNormalization S hS hcarrier yStar p t ht hQ⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
