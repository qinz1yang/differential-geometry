import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.FrameEquivalence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorClosedIntervalRank

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem curvatureOperator_rank_spatially_constant_and_locally_constant_from_left_on_closed_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a T : ℝ} (ha : a < 0) (hT : 0 < T)
    (hcarrier : Icc a T ⊆ D.carrier) (hregular : Ioo a T ⊆ D.regular)
    (hdim : Module.finrank ℝ E = 3)
    (hR : ∀ t ∈ Icc 0 T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    let rank := fun t x => Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
    (∀ t ∈ Ioc 0 T, ∀ x y, rank t x = rank t y) ∧
    (∀ x, MonotoneOn (fun t => rank t x) (Ioc 0 T)) ∧
    (∀ t ∈ Ioc 0 T, ∀ x, ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
      rank s x = rank t x) ∧
    ∃ δ ∈ Ioc 0 T, ∃ q : ℕ, ∀ t ∈ Ioc 0 δ, ∀ x, rank t x = q := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : NeZero (Module.finrank ℝ E) := ⟨by omega⟩
  let basisAt : ∀ x : M, Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    fun _ => Module.finBasis ℝ E
  obtain ⟨ι, hι₀, -, hframe, hgram, hι⟩ :=
    exists_uhlenbeckFrame_contMDiffOn_closed S hS ha hT hcarrier hregular basisAt
  obtain ⟨U, -, -, hU, hode, hmetric⟩ :=
    exists_uhlenbeck_isometry_eq_endomorphism_on_Icc S hT basisAt ι hι₀ hframe hgram hι
  let h := S.family.metric 0
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨h.toRiemannianMetric⟩
  let sourceNorm : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      y
  let : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := sourceNorm
  let : ∀ y : M, SeminormedAddCommGroup (TangentSpace I y) :=
    fun y => (sourceNorm y).toSeminormedAddCommGroup
  let : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) :=
    fun y => Bundle.instInnerProductSpaceReal y
  let : ∀ y : M, NormedSpace ℝ (TangentSpace I y) := fun _ => InnerProductSpace.toNormedSpace
  let : IsContMDiffRiemannianBundle I ∞ E (TangentSpace I) :=
    ⟨h.inner, h.contMDiff, fun _ _ _ => rfl⟩
  apply curvatureOperator_rank_spatially_constant_and_locally_constant_from_left_of_uhlenbeck_Icc
    (F := E) (V := TangentSpace I) S hS hdim hT
    (fun t ht => hcarrier ⟨ha.le.trans ht.1, ht.2⟩)
    (fun t ht => hregular ⟨ha.trans ht.1, ht.2⟩)
    (solution_metric_tensor_contMDiffOn_closed S hS ha hT hcarrier hregular) U hU
  · exact hmetric
  · intro x v t ht
    exact (hode t ht x v).hasDerivWithinAt
  · exact hR

end DifferentialGeometry.PDE.RicciFlow
