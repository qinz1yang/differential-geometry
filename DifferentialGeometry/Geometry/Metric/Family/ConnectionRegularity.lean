import DifferentialGeometry.Analysis.Calculus.TimeJet.Commutation
import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.Christoffel
import DifferentialGeometry.Geometry.Connection.LeviCivita.Chart.Local
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold DifferentialGeometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor.Coordinates
open scoped Manifold ContDiff Topology BigOperators
namespace DifferentialGeometry.PDE.RicciFlow
section ChartGram
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem chartGramOnE_set
    (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ) (α : M)
    (hsmooth : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (I := I) (g p.1) x₀ p.2 i j)
        (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞
      (fun p : ℝ × E =>
        DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) (g p.1) α i j p.2)
      (J ×ˢ interior ((extChartAt I α).target)) := by
  classical
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm (extChartAt I α).target :=
    contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹' (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hσ1 : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × E => p.1)
    (J ×ˢ interior ((extChartAt I α).target)) :=
    (contMDiff_iff_contDiff.mpr contDiff_fst).contMDiffOn
  have hsnd : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E) ∞ (fun p : ℝ × E => p.2)
      (J ×ˢ interior ((extChartAt I α).target)) :=
    (contMDiff_iff_contDiff.mpr contDiff_snd).contMDiffOn
  have hmaps2 : Set.MapsTo (fun p : ℝ × E => p.2)
      (J ×ˢ interior ((extChartAt I α).target)) (extChartAt I α).target :=
    fun p hp => interior_subset hp.2
  have hσ2 : ContMDiffOn 𝓘(ℝ, ℝ × E) I ∞
      (fun p : ℝ × E => (extChartAt I α).symm p.2) (J ×ˢ interior ((extChartAt I α).target)) :=
    hsymm.comp hsnd hmaps2
  have hσ : ContMDiffOn 𝓘(ℝ, ℝ × E) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × E => (p.1, (extChartAt I α).symm p.2))
        (J ×ˢ interior ((extChartAt I α).target)) :=
    hσ1.prodMk hσ2
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ × E) 𝓘(ℝ) ∞
      (fun p : ℝ × E =>
        DifferentialGeometry.Geometry.Operator.chartGramOnE (I := I) (g p.1) α i j p.2)
          (J ×ˢ interior ((extChartAt I α).target)) := by
    refine ((hsmooth α i j).comp hσ (fun p hp => ⟨hp.1, hsubset (interior_subset hp.2)⟩)).congr ?_
    intro p _
    rfl
  exact hcomp.contDiffOn

end ChartGram

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (g : ℝ → SmoothRiemannianMetric I M) (J : Set ℝ)
  (hgram : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
      (J ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))

include hgram in
theorem metricFlatModel_contDiffOn (x₀ : M) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      DifferentialGeometry.Geometry.Connection.metricFlatModelInChart (g p.1) x₀ p.2)
      (J ×ˢ interior (extChartAt I x₀).target) := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  let B := DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  have hs : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        (B.repr v i * B.repr w j) * chartGramOnE (g p.1) x₀ i j p.2)
      (J ×ˢ interior (extChartAt I x₀).target) :=
    ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      contDiffOn_const.mul (chartGramOnE_set g J x₀ hgram i j)
  apply hs.congr
  intro p hp
  let A := DifferentialGeometry.Geometry.Connection.metricFlatModelInChart (g p.1) x₀ p.2
  have hbase (i j : Fin (Module.finrank ℝ E)) : A (B i) (B j) =
      chartGramOnE (g p.1) x₀ i j p.2 := by
    rw [DifferentialGeometry.Geometry.Connection.metricFlatModelInChart_apply_of_target
      (g p.1) x₀ (interior_subset hp.2)]
    rfl
  change A v w = _
  calc
    A v w = A (∑ i, B.repr v i • B i) (∑ j, B.repr w j • B j) := by
      rw [B.sum_repr, B.sum_repr]
    _ = ∑ i, ∑ j, (B.repr v i * B.repr w j) * chartGramOnE (g p.1) x₀ i j p.2 := by
      simp only [map_sum, map_smul, sum_apply, smul_apply,
        smul_eq_mul, Finset.mul_sum, hbase]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

variable [CompleteSpace E]
include hgram in
theorem inverseFlatModel_contDiffOn (x₀ : M) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => ContinuousLinearMap.inverse
      (DifferentialGeometry.Geometry.Connection.metricFlatModelInChart (g p.1) x₀ p.2))
      (J ×ˢ interior (extChartAt I x₀).target) := by
  intro p hp
  have hi : ContDiffAt ℝ ∞ (fun A : E →L[ℝ] (E →L[ℝ] ℝ) => A.inverse)
      (DifferentialGeometry.Geometry.Connection.metricFlatModelInChart (g p.1) x₀ p.2) :=
    (metricFlatModelInChart_isInvertible_of_mem (g p.1) x₀ (interior_subset hp.2)).contDiffAt_map_inverse
  exact hi.comp_contDiffWithinAt
    (f := fun q : ℝ × E => DifferentialGeometry.Geometry.Connection.metricFlatModelInChart (g q.1) x₀ q.2)
    p (metricFlatModel_contDiffOn g J hgram x₀ p hp)

variable [I.Boundaryless]
include hgram in
theorem connectionModel_contDiffOn (hJ : UniqueDiffOn ℝ J) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := ℝ) E) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => leviCivitaChristoffelModelRHS (g p.1) x₀ i j k p.2)
      (J ×ˢ interior (extChartAt I x₀).target) := by
  have hf (a b : CoordinateIdx (𝕜 := ℝ) E) :
      ContDiffOn ℝ ∞ (fun p : ℝ × E => metricFlatModelInChartComponent (g p.1) x₀ a b p.2)
        (J ×ˢ interior (extChartAt I x₀).target) :=
    ((metricFlatModel_contDiffOn g J hgram x₀).clm_apply
      (contDiffOn_const (c := (Module.finBasis ℝ E) a))).clm_apply
      (contDiffOn_const (c := (Module.finBasis ℝ E) b))
  have hd (a b m : CoordinateIdx (𝕜 := ℝ) E) :
      ContDiffOn ℝ ∞ (fun p : ℝ × E => fderivWithin ℝ
        (metricFlatModelInChartComponent (g p.1) x₀ a b) (Set.range I) p.2
        ((Module.finBasis ℝ E) m)) (J ×ˢ interior (extChartAt I x₀).target) := by
    have hh := (spatialFDeriv_contDiffOn
      (G := fun t y => metricFlatModelInChartComponent (g t) x₀ a b y)
      hJ isOpen_interior (hf a b)).clm_apply (contDiffOn_const (c := (Module.finBasis ℝ E) m))
    rw [I.range_eq_univ]
    simp only [fderivWithin_univ]
    exact hh
  have hinv (a b : CoordinateIdx (𝕜 := ℝ) E) :
      ContDiffOn ℝ ∞ (fun p : ℝ × E => (Module.finBasis ℝ E).coord a
        (ContinuousLinearMap.inverse
          (DifferentialGeometry.Geometry.Connection.metricFlatModelInChart (g p.1) x₀ p.2)
          (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord b))))
        (J ×ˢ interior (extChartAt I x₀).target) := by
    exact (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord a)).contDiff.comp_contDiffOn
      ((inverseFlatModel_contDiffOn g J hgram x₀).clm_apply
        (contDiffOn_const (c := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord b))))
  unfold leviCivitaChristoffelModelRHS
  exact contDiffOn_const.mul (ContDiffOn.sum fun l _ =>
    (hinv k l).mul (((hd j l i).add (hd i l j)).sub (hd i j l)))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
theorem coordinate_model_contMDiffOn {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (x₀ : M) (f : ℝ × E → F)
    (hf : ContDiffOn ℝ ∞ f (J ×ˢ interior (extChartAt I x₀).target)) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, F) ∞
      (fun p : ℝ × M => f (p.1, extChartAt I x₀ p.2))
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
  have hm : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ × E) ∞
      (fun p : ℝ × M => (p.1, extChartAt I x₀ p.2))
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
    intro p hp
    rw [contMDiffWithinAt_prod_module_iff]
    refine ⟨contMDiffWithinAt_fst, ?_⟩
    have hx : p.2 ∈ (chartAt H x₀).source := by
      rw [← extChartAt_source_eq_chartAt_source (I := I)]
      exact chartLeviCivitaGoodSet_mem_extChartAt_source hp.2
    exact ((contMDiffAt_extChartAt' (I := I) (n := ∞) hx).comp p contMDiffAt_snd).contMDiffWithinAt
  exact hf.contMDiffOn.comp hm (fun p hp =>
    ⟨hp.1, chartLeviCivitaGoodSet_extChartAt_mem_interior hp.2⟩)

include hgram in
theorem connectionComponents_contMDiffOn (hJ : UniqueDiffOn ℝ J) (x₀ : M)
    (i j k : CoordinateIdx (𝕜 := ℝ) E) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => christoffelSymbolInFrame (leviCivitaConnectionOfMetric (g p.1))
        (coordinateFrameAt (I := I) x₀) (coordinateFrameAt_isLocalFrame_one (I := I) x₀) p.2 i j k)
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
  have hh := coordinate_model_contMDiffOn J x₀
    (fun p : ℝ × E => leviCivitaChristoffelModelRHS (g p.1) x₀ i j k p.2)
    (connectionModel_contDiffOn g J hgram hJ x₀ i j k)
  apply hh.congr
  intro p hp
  exact (leviCivitaChristoffelModelRHS_eq_christoffel_of_mem (g p.1) x₀
    (chartLeviCivitaGoodSet_mem_baseSet hp.2) i j k).symm

omit [I.Boundaryless] in
include hgram in
theorem inverseComponents_contMDiffOn (x₀ : M) (i j : CoordinateIdx (𝕜 := ℝ) E) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => inverseMetricFlatModelInChartComponent (g p.1) x₀ i j (extChartAt I x₀ p.2))
      (J ×ˢ chartLeviCivitaGoodSet (I := I) x₀) := by
  apply coordinate_model_contMDiffOn (I := I) J x₀
    (fun p : ℝ × E => inverseMetricFlatModelInChartComponent (g p.1) x₀ i j p.2)
  exact (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).contDiff.comp_contDiffOn
    ((inverseFlatModel_contDiffOn g J hgram x₀).clm_apply
      (contDiffOn_const (c := LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord j))))

end DifferentialGeometry.PDE.RicciFlow
