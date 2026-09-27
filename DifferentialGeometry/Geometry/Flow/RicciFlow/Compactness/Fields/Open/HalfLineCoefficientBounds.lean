import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.ClosedHalfLineSolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedRegularity
import DifferentialGeometry.Geometry.Metric.Family.Regularity.JointDifferentialOperator
import DifferentialGeometry.Geometry.Metric.Family.ChartCurvature.WithinSmoothness
import DifferentialGeometry.Geometry.Connection.ChartBridge.Curvature.BasisIdentityOffCenter
import Mathlib.Analysis.Normed.Group.Bounded


noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem HalfLineMetricConvergenceData.exists_chart_coefficient_bound_on_closed_band
    (Phi : PointedCGHMaps X P subseq) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    (hcarrier : X.D.carrier = Iic 0) (hregular : Iio 0 ⊆ X.D.regular)
    (α : P.M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I α).target) {T : ℝ} (hT : 1 < T) :
    ∃ B : ℝ≥0, ∀ θ ∈ Icc 1 T, ∀ y ∈ K,
      (∀ i j : Fin (Module.finrank ℝ E),
        |(co.gInf (1 - θ)).inner ((extChartAt I α).symm y)
          (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
          (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))| ≤ B) ∧
      (∀ i j : Fin (Module.finrank ℝ E),
        |ricciTensor (co.gInf (1 - θ)) ((extChartAt I α).symm y)
          (chartBasisVecFiber (I := I) α i ((extChartAt I α).symm y))
          (chartBasisVecFiber (I := I) α j ((extChartAt I α).symm y))| ≤ B) ∧
      (∀ i j k : Fin (Module.finrank ℝ E),
        |chartChristoffel (co.gInf (1 - θ)) α i j k y| ≤ B) := by
  classical
  let S : SolutionOn (I := I) (M := P.M) X.D := { base := { metric := co.gInf } }
  have hS : IsSolutionOn S := co.isSolutionOn Phi hcarrier hregular
  have hab : (1 - T) - 1 < 1 - T := sub_lt_self _ zero_lt_one
  have hb : 1 - T < 0 := sub_neg.mpr hT
  have hslab : Icc ((1 - T) - 1) 0 ⊆ X.D.carrier := by
    rw [hcarrier]
    exact Icc_subset_Iic_self
  have hreg : Ioo ((1 - T) - 1) 0 ⊆ X.D.regular :=
    Ioo_subset_Iio_self.trans hregular
  have hmet := solution_metricCLMSection_contMDiffOn_closed S hS hab hb hslab hreg
  have hgram (i j : Fin (Module.finrank ℝ E)) : ContDiffOn ℝ ∞
      (fun z : ℝ × E => chartGramOnE (co.gInf z.1) α i j z.2)
      (Icc (1 - T) 0 ×ˢ interior (extChartAt I α).target) :=
    chartGramOnE_contDiffOn_of_contMDiffOn co.gInf hmet α i j
  have hwithin : chartGramFamilySmoothWithinOn co.gInf α (Icc (1 - T) 0) := by
    intro i j t y ht hy
    exact hgram i j (t, y) ⟨ht, hy⟩
  let V : ℝ × E → (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      Fin (Module.finrank ℝ E) → ℝ × ℝ × ℝ) := fun z ijk =>
    (chartGramOnE (co.gInf z.1) α ijk.1 ijk.2.1 z.2,
      chartRicciTensor (co.gInf z.1) α ijk.1 ijk.2.1 z.2,
      chartChristoffel (co.gInf z.1) α ijk.1 ijk.2.1 ijk.2.2 z.2)
  have hV : ContinuousOn V (Icc (1 - T) 0 ×ˢ interior (extChartAt I α).target) := by
    apply continuousOn_pi.mpr
    intro ijk
    apply (hgram ijk.1 ijk.2.1).continuousOn.prodMk
    apply ContinuousOn.prodMk
    · intro z hz
      exact (chartRicciTensor_contDiffWithinAt co.gInf α hwithin
        ijk.1 ijk.2.1 hz.1 hz.2).continuousWithinAt
    · intro z hz
      exact (chartChristoffel_contDiffWithinAt co.gInf α hwithin
        ijk.1 ijk.2.1 ijk.2.2 hz.1 hz.2).continuousWithinAt
  have hKi : K ⊆ interior (extChartAt I α).target := by
    rwa [(isOpen_extChartAt_target (I := I) α).interior_eq]
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hV.mono (prod_mono Subset.rfl hKi))
  let B : ℝ≥0 := ⟨max 0 C, le_max_left _ _⟩
  refine ⟨B, ?_⟩
  intro θ hθ y hy
  have ht : 1 - θ ∈ Icc (1 - T) 0 := ⟨by linarith [hθ.2], by linarith [hθ.1]⟩
  have hnorm (i j k : Fin (Module.finrank ℝ E)) :
      ‖V (1 - θ, y) (i, j, k)‖ ≤ (B : ℝ) :=
    (norm_le_pi_norm _ _).trans ((hC (1 - θ, y) ⟨ht, hy⟩).trans (le_max_right _ _))
  have hgood : (extChartAt I α).symm y ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
    exact (extChartAt I α).map_target (hKt hy)
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    change |chartGramOnE (co.gInf (1 - θ)) α i j y| ≤ B
    simpa only [V, Real.norm_eq_abs] using
      (norm_fst_le (V (1 - θ, y) (i, j, 0))).trans (hnorm i j 0)
  · intro i j
    rw [ricciTensor_chartBasisVec_alpha_eq (co.gInf (1 - θ)) α i j hgood,
      (extChartAt I α).right_inv (hKt hy)]
    simpa only [V, Real.norm_eq_abs] using
      (norm_fst_le ((V (1 - θ, y) (i, j, 0)).2)).trans
        ((norm_snd_le (V (1 - θ, y) (i, j, 0))).trans (hnorm i j 0))
  · intro i j k
    simpa only [V, Real.norm_eq_abs] using
      (norm_snd_le ((V (1 - θ, y) (i, j, k)).2)).trans
        ((norm_snd_le (V (1 - θ, y) (i, j, k))).trans (hnorm i j k))

end DifferentialGeometry.CheegerGromovCompactness
