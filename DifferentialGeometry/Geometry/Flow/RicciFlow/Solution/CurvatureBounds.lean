import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Data.UniformBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Basic
import DifferentialGeometry.Geometry.Metric.Family.Regularity.Pair
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness
import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Metric.Family.TensorNorm

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Integral.Measure
open scoped _root_.Manifold ContDiff

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

private theorem exists_curvature_bound_on_closed_interval_of_innerProductSpace
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hreg : Icc a b ⊆ D.regular) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x : M,
      normSq0S (S.family.metric t) x 4 (metricRm04At (S.family.metric t) x) ≤ C := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (S.family.metric p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc a b ×ˢ (Set.univ : Set M)) := by
    intro p hp
    exact (hS.smoothMetric.metricCLMSmoothAt
      (D.regular_isOpen.mem_nhds (hreg hp.1))).contMDiffWithinAt
  have hgram := chartGramMatrix_joint_contMDiffOn S.family.metric (Icc a b) hmetric
  exact rm04SlabSup S.family.metric S.family.metric S.family.metric hgram hgram hgram


end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]

theorem exists_curvature_bound_on_closed_interval_of_isSolutionOn
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hreg : Icc a b ⊆ D.regular) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x : M,
      normSq0S (S.family.metric t) x 4 (metricRm04At (S.family.metric t) x) ≤ C := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (Module.finBasis ℝ E).equivFun.toContinuousLinearEquiv.trans
      (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm
  let J := I.transContinuousLinearEquiv e
  let Φ := ContinuousLinearEquiv.toTransContinuousLinearEquiv (n := ∞) I M e
  let U : SolutionOn (I := J) (M := M) D := S.pullback Φ.symm
  have hU : IsSolutionOn U := hS.pullback S Φ.symm
  obtain ⟨C, hC, hbound⟩ :=
    exists_curvature_bound_on_closed_interval_of_innerProductSpace U hU hreg
  refine ⟨C, hC, fun t ht x => ?_⟩
  have hb := hbound t ht x
  change normSq0S (Diffeomorph.pullbackMetricCross (S.family.metric t) Φ.symm) x 4
    (metricRm04At (Diffeomorph.pullbackMetricCross (S.family.metric t) Φ.symm) x) ≤ C at hb
  rw [DifferentialGeometry.CheegerGromovCompactness.riemannNormSq_cross] at hb
  exact hb

omit [I.Boundaryless] in
theorem exists_curvature_bound_on_carrier_interval_of_isSolutionOn
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hsub : Set.Icc a b ⊆ D.carrier) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ∀ x : M,
      normSq0S (S.family.metric t) x 4 (metricRm04At (S.family.metric t) x) ≤ C := by
  have hg : tensor0SFamilyContinuousOnSet (I := I) (M := M) 2 (Set.Icc a b)
      (fun t x => metricTensorField (I := I) (S.base.metric t) x) := by
    have hmono := tensor0SFamilyContinuousOnSet.mono (I := I) (M := M)
      hS.smoothMetric.metricTensor_cont (by intro s hs; exact hsub hs)
    refine tensor0SFamilyContinuousOnSet.congr (I := I) (M := M) hmono ?_
    intro t _ x
    rfl
  have hA : tensor0SFamilyContinuousOnSet (I := I) (M := M) 4 (Set.Icc a b)
      (fun t x => S.base.rm04 t x) :=
    tensor0SFamilyContinuousOnSet.mono (I := I) (M := M) hS.rm04Cont
      (by intro s hs; exact hsub hs)
  obtain ⟨C, hC⟩ := (isCompact_univ :
      IsCompact (Set.univ : Set ({t : ℝ // t ∈ Set.Icc a b} × M))).exists_bound_of_continuousOn
    (continuous_normSq0S_family (I := I) S.base.metric
      (fun t x => S.base.rm04 t x) hg hA).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t ht x => ?_⟩
  have h := hC (⟨t, ht⟩, x) (Set.mem_univ _)
  rw [Real.norm_eq_abs] at h
  have hfin : normSq0S (I := I) (S.base.metric t) x 4 (S.base.rm04 t x) ≤ max C 0 :=
    (le_abs_self _).trans (h.trans (le_max_left _ _))
  simpa only [SolutionFamily.rm04, metricRm04_apply, SolutionOn.family_metric] using hfin

end DifferentialGeometry.PDE.RicciFlow
