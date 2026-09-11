import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderChartMetric
import DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Koszul
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Geometry.Metric.DeTurck.ConnectionDifference.Basic
import DifferentialGeometry.Geometry.Connection.TensorNabla.Connection.Endomorphism


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open Bundle Manifold Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff _root_.Topology BigOperators

private abbrev SphereModel := EuclideanSpace ℝ (Fin 2)
private abbrev CylinderModel := SphereModel × ℝ

private local instance cylinderConnectionSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩


theorem shrinkingCylinder_chartChristoffelContraction (s : ℝ) (hs : s < 1)
    (p : SpatialNeckCylinder) (y : CylinderModel)
    (hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target) (v w : CylinderModel) :
    chartChristoffelContraction (scalarOneShrinkingCylinderMetric s hs) p v w y =
      (chartChristoffelContraction
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1 v.1 w.1 y.1, 0) := by
  have hsource := (extChartAt SpatialNeckCylinderModel p).map_target hy
  rw [extChartAt_source] at hsource
  have hyint : y ∈ interior (extChartAt SpatialNeckCylinderModel p).target := by
    rw [(isOpen_extChartAt_target (I := SpatialNeckCylinderModel) p).interior_eq]
    exact hy
  have hyprod := hy
  rw [extChartAt_prod] at hyprod
  have hysphere : y.1 ∈ interior (extChartAt (𝓡 2) p.1).target := by
    rw [(isOpen_extChartAt_target (I := 𝓡 2) p.1).interior_eq]
    exact hyprod.1
  apply chartGramBilin_injective_on_source (scalarOneShrinkingCylinderMetric s hs) p hsource
  apply ContinuousLinearMap.ext
  intro u
  calc
    _ = MetricKoszul.koszulCov
        (fderiv ℝ (fun z => chartGramBilin (scalarOneShrinkingCylinderMetric s hs) p
          ((extChartAt SpatialNeckCylinderModel p).symm z)) y) v w u :=
      DFunLike.congr_fun (chartChristoffelContraction_flat_eq_koszul
        (scalarOneShrinkingCylinderMetric s hs) p hyint v w) u
    _ = (2 * (1 - s)) * MetricKoszul.koszulCov
        (fderiv ℝ (fun z => chartGramBilin
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1
          ((extChartAt (𝓡 2) p.1).symm z)) y.1) v.1 w.1 u.1 := by
      rw [shrinkingCylinder_chartGramBilin_fderiv s hs p y hy]
      exact koszulCov_lineProduct _ _ u v w
    _ = (2 * (1 - s)) * chartGramBilin
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1
          ((extChartAt (𝓡 2) p.1).symm y.1)
          (chartChristoffelContraction
            (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1 v.1 w.1 y.1) u.1 :=
      congrArg (fun r : ℝ => (2 * (1 - s)) * r)
        (DFunLike.congr_fun (chartChristoffelContraction_flat_eq_koszul
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) p.1 hysphere v.1 w.1) u.1).symm
    _ = _ := by
      rw [shrinkingCylinder_chartGramBilin_in_coordinates s hs p y hy]
      simp only [lineProductMetricForm_apply, zero_mul, add_zero]


theorem shrinkingCylinder_chartChristoffel_eq (s t : ℝ) (hs : s < 1) (ht : t < 1)
    (p : SpatialNeckCylinder) (y : CylinderModel)
    (hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target)
    (i j k : Fin (Module.finrank ℝ CylinderModel)) :
    chartChristoffel (scalarOneShrinkingCylinderMetric s hs) p i j k y =
      chartChristoffel (scalarOneShrinkingCylinderMetric t ht) p i j k y := by
  classical
  have hcontraction :=
    (shrinkingCylinder_chartChristoffelContraction s hs p y hy
      (chartModelBasis CylinderModel i) (chartModelBasis CylinderModel j)).trans
    (shrinkingCylinder_chartChristoffelContraction t ht p y hy
      (chartModelBasis CylinderModel i) (chartModelBasis CylinderModel j)).symm
  have hcoord := congrArg (fun v => (chartModelBasis CylinderModel).repr v k) hcontraction
  simpa only [chartChristoffelContraction, chartCoord,
    Module.Basis.repr_self_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Module.Basis.repr_sum_self] using hcoord


theorem shrinkingCylinder_leviCivita_apply_eq (s t : ℝ) (hs : s < 1) (ht : t < 1)
    (x : SpatialNeckCylinder)
    (sigma : (y : SpatialNeckCylinder) → TangentSpace SpatialNeckCylinderModel y)
    (hsigma : MDifferentiableAt SpatialNeckCylinderModel SpatialNeckCylinderModel.tangent
      (T% sigma) x) (v : TangentSpace SpatialNeckCylinderModel x) :
    leviCivitaConnectionOfMetric (scalarOneShrinkingCylinderMetric s hs) sigma x v =
      leviCivitaConnectionOfMetric (scalarOneShrinkingCylinderMetric t ht) sigma x v := by
  have hx := self_mem_chartLeviCivitaGoodSet (I := SpatialNeckCylinderModel) x
  have htarget := (extChartAt SpatialNeckCylinderModel x).map_source (mem_extChartAt_source x)
  have hcorrection : christoffelCorrection (scalarOneShrinkingCylinderMetric s hs) x x
        (chartESectionRepr (I := SpatialNeckCylinderModel) x sigma x) v =
      christoffelCorrection (scalarOneShrinkingCylinderMetric t ht) x x
        (chartESectionRepr (I := SpatialNeckCylinderModel) x sigma x) v := by
    simp only [christoffelCorrection_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [shrinkingCylinder_chartChristoffel_eq s t hs ht x _ htarget i j k]
  calc
    _ = chartLeviCivita (scalarOneShrinkingCylinderMetric s hs) x sigma x v :=
      LeviCivita_chart_apply (scalarOneShrinkingCylinderMetric s hs) x hx hsigma v
    _ = chartLeviCivita (scalarOneShrinkingCylinderMetric t ht) x sigma x v := by
      rw [chartLeviCivita_apply _ x sigma hx v, chartLeviCivita_apply _ x sigma hx v,
        hcorrection]
    _ = _ := (LeviCivita_chart_apply (scalarOneShrinkingCylinderMetric t ht) x hx hsigma v).symm


theorem shrinkingCylinder_connectionDifference_eq_zero
    (s t : ℝ) (hs : s < 1) (ht : t < 1) :
    DifferentialGeometry.PDE.DeTurck.connectionDifference
      (scalarOneShrinkingCylinderMetric s hs) (scalarOneShrinkingCylinderMetric t ht) = 0 := by
  classical
  funext x
  apply ContinuousLinearMap.ext
  intro w
  apply ContinuousLinearMap.ext
  intro v
  obtain ⟨sigma, hsigma⟩ := ContMDiffSection.exists_eq_at
    (I := SpatialNeckCylinderModel) (n := (⊤ : ℕ∞))
    (F := CylinderModel) (V := (TangentSpace SpatialNeckCylinderModel : SpatialNeckCylinder → Type _)) x w
  have hdiff := DifferentialGeometry.PDE.DeTurck.connectionDifference_apply
    (scalarOneShrinkingCylinderMetric s hs) (scalarOneShrinkingCylinderMetric t ht)
    sigma.mdifferentiableAt v
  have heq := shrinkingCylinder_leviCivita_apply_eq s t hs ht x (fun y => sigma y)
    sigma.mdifferentiableAt v
  have hzero : DifferentialGeometry.PDE.DeTurck.connectionDifference
      (scalarOneShrinkingCylinderMetric s hs) (scalarOneShrinkingCylinderMetric t ht)
        x (sigma x) v = 0 := hdiff.trans (sub_eq_zero.mpr heq)
  simpa only [hsigma, Pi.zero_apply, zero_apply] using hzero


theorem shrinkingCylinder_connectionEndomorphism_eq
    (s t : ℝ) (hs : s < 1) (ht : t < 1) (p : SpatialNeckCylinder) (y : CylinderModel) :
    DifferentialGeometry.TensorLieDeriv.connectionEndomorphismInChartL
      (leviCivitaConnectionOfMetric (scalarOneShrinkingCylinderMetric s hs)) p y =
    DifferentialGeometry.TensorLieDeriv.connectionEndomorphismInChartL
      (leviCivitaConnectionOfMetric (scalarOneShrinkingCylinderMetric t ht)) p y := by
  classical
  apply ContinuousLinearMap.ext
  intro X
  apply ContinuousLinearMap.ext
  intro v
  by_cases hy : y ∈ (extChartAt SpatialNeckCylinderModel p).target
  · rw [DifferentialGeometry.TensorLieDeriv.connectionEndomorphismInChartL_apply_of_mem _ p hy,
      DifferentialGeometry.TensorLieDeriv.connectionEndomorphismInChartL_apply_of_mem _ p hy]
    have hbase : (extChartAt SpatialNeckCylinderModel p).symm y ∈
        (trivializationAt CylinderModel (TangentSpace SpatialNeckCylinderModel) p).baseSet := by
      simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
        (extChartAt SpatialNeckCylinderModel p).map_target hy
    apply congrArg
    exact shrinkingCylinder_leviCivita_apply_eq s t hs ht _ _
      (DifferentialGeometry.TensorLieDeriv.mdifferentiableAt_tangentConstInChart_of_mem
        v hbase) _
  · rw [DifferentialGeometry.TensorLieDeriv.connectionEndomorphismInChartL_apply_of_notMem _ p hy,
      DifferentialGeometry.TensorLieDeriv.connectionEndomorphismInChartL_apply_of_notMem _ p hy]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
