import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.NonnegativeCurvatureScalarNorm

set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set MeasureTheory
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  (F : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval)

local instance routeBSourceTopology : TopologicalSpace F.M := F.topology
local instance routeBSourceCharted : ChartedSpace H F.M := F.charted
local instance routeBSourceSmooth : IsManifold I ∞ F.M := F.smooth
local instance routeBSourceC1 : IsManifold I 1 F.M :=
  IsManifold.of_le (I := I) (M := F.M) (n := (∞ : WithTop ℕ∞))
    (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
local instance routeBSourceT2 : T2Space F.M := F.t2
local instance routeBSourceTangentT2 : T2Space (TangentBundle I F.M) := F.t2TangentBundle
local instance routeBSourceSigma : SigmaCompactSpace F.M := F.sigmaCompact

theorem terminalTime_not_mem_regular
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
    (hcarrier : D.carrier = Set.Iic 0) :
    (0 : ℝ) ∉ D.regular := by
  intro h0
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp (D.regular_isOpen.mem_nhds h0)
  have hpos : (0 : ℝ) < eps / 2 := by linarith
  have hdist : dist (eps / 2) (0 : ℝ) < eps := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
    linarith
  have hreg : eps / 2 ∈ D.regular := hball hdist
  have hmem : eps / 2 ∈ D.carrier := D.regular_subset hreg
  rw [hcarrier] at hmem
  exact absurd (Set.mem_Iic.mp hmem) (not_le.mpr hpos)

theorem ancientTimeInterval_terminal_not_regular :
    (0 : ℝ) ∉ ancientTimeInterval.regular :=
  terminalTime_not_mem_regular ancientTimeInterval rfl

theorem ancientTimeInterval_slab_not_regular {tau : ℝ} (htau : 0 < tau) :
    ¬ (Set.Icc (0 - tau) 0 ⊆ ancientTimeInterval.regular) := by
  intro hslab
  exact ancientTimeInterval_terminal_not_regular (hslab ⟨by linarith, le_rfl⟩)

theorem ancientTimeInterval_slab_not_regular_of_carrier
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) {tau : ℝ}
    (hcarrier : D.carrier = Set.Iic 0) (htau : 0 < tau) :
    ¬ (Set.Icc (0 - tau) 0 ⊆ D.regular) := by
  intro hslab
  exact terminalTime_not_mem_regular D hcarrier (hslab ⟨by linarith, le_rfl⟩)

omit [I.Boundaryless] in
theorem ancientKappa_rmNormLeScalar_finrank {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) :
    PointedFlowRmNormLeScalar (I := I) F ((Module.finrank ℝ E : ℝ) ^ 2) := by
  intro t ht x
  have hoperator :
      metricAlgebraicCurvatureTensorAt (I := I) (F.S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := F.M) := by
    apply mem_algebraicCurvatureOperatorNonnegativeCone.mpr
    intro n c v w
    have h := hF.nonnegativeCurvatureOperator t ht x n c v w
    simpa only [algebraicCurvatureOperatorQuadraticEval, metricAlgebraicCurvatureTensorAt,
      tensor04StandardAt, SolutionFamily.rm04, metricRm04_apply] using h
  have hbound := sqrt_metricRm_normSq_le_finrank_sq_mul_scalar (I := I)
    (F.S.base.metric t) x hoperator
  simpa only [PointedFlowData.rmNormSq, SolutionOn.family, SolutionFamily.rm04,
    metricRm04_apply, SolutionOn.scalar, SolutionFamily.scalar] using hbound

omit [I.Boundaryless] in
theorem ancientKappa_rmNormSqBounded_finrank {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) :
    ∃ K : ℝ, ∀ t ∈ ancientTimeInterval.carrier, ∀ x : F.M,
      normSq0S (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x) ≤ K := by
  obtain ⟨C, hC⟩ := hF.globalScalarBound
  refine ⟨((Module.finrank ℝ E : ℝ) ^ 2 * C) ^ 2, ?_⟩
  intro t ht x
  have hle := ancientKappa_rmNormLeScalar_finrank (I := I) F hF t ht x
  have hscalar : F.S.scalar t x ≤ C := (hC t ht x).2
  have hsqrt : Real.sqrt (F.rmNormSq (I := I) t x) ≤
      (Module.finrank ℝ E : ℝ) ^ 2 * C :=
    hle.trans (mul_le_mul_of_nonneg_left hscalar (sq_nonneg _))
  have hnonneg : 0 ≤ F.rmNormSq (I := I) t x := by
    simpa only [PointedFlowData.rmNormSq, SolutionOn.family] using
      normSq0S_nonneg (I := I) (F.S.base.metric t) x 4 (F.S.base.rm04 t x)
  have hsq : Real.sqrt (F.rmNormSq (I := I) t x) ^ 2 = F.rmNormSq (I := I) t x :=
    Real.sq_sqrt hnonneg
  have hfinal : F.rmNormSq (I := I) t x ≤
      ((Module.finrank ℝ E : ℝ) ^ 2 * C) ^ 2 := by
    nlinarith [Real.sqrt_nonneg (F.rmNormSq (I := I) t x)]
  simpa only [PointedFlowData.rmNormSq, SolutionOn.family, SolutionFamily.rm04,
    metricRm04_apply] using hfinal

omit [I.Boundaryless] in
theorem ancientKappa_regularSlabBound_finrank {kappa : ℝ}
    (hF : IsAncientKappaSolution kappa F) (a b : ℝ)
    (hslab : Set.Icc a b ⊆ ancientTimeInterval.regular) :
    ∃ K : ℝ, ∀ t ∈ Set.Icc a b, ∀ z : F.M,
      normSq0S (I := I) (F.S.base.metric t) z 4 (F.S.base.rm04 t z) ≤ K := by
  obtain ⟨K, hK⟩ := ancientKappa_rmNormSqBounded_finrank (I := I) F hF
  exact ⟨K, fun t ht z => hK t (ancientTimeInterval.regular_subset (hslab ht)) z⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
