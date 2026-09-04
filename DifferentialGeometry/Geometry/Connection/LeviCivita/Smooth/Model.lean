import DifferentialGeometry.Geometry.Connection.LeviCivita.Smooth.MetricCoord
import DifferentialGeometry.Geometry.Coordinates.MetricCompatibility.Inverse
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator

set_option autoImplicit false

noncomputable section


namespace DifferentialGeometry.Geometry.Connection

open Bundle
open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

noncomputable def metricFlatContinuousEquiv
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    E ≃L[Real] (E →L[Real] Real) :=
  Tensor.Coordinates.metricFlatContinuousEquiv (I := I) g x₀

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatContinuousEquiv_apply
    (g : SmoothRiemannianMetric I M) (x₀ : M) (v w : E) :
    ((metricFlatContinuousEquiv (I := I) g x₀) v) w =
      g.inner x₀
        ((trivializationAt E (TangentSpace I) x₀).symmL Real x₀ v)
        ((trivializationAt E (TangentSpace I) x₀).symmL Real x₀ w) :=
  Tensor.Coordinates.metricFlatContinuousEquiv_apply (I := I) g x₀ v w

noncomputable def metricFlatModelInChart
    (g : SmoothRiemannianMetric I M) (x₀ : M) (y : E) :
    E →L[Real] E →L[Real] Real :=
  Tensor.Coordinates.metricFlatModelInChart (I := I) g x₀ y

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_center_eq
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀) =
      (metricFlatContinuousEquiv (I := I) g x₀ :
        E →L[Real] (E →L[Real] Real)) :=
  Tensor.Coordinates.metricFlatModelInChart_center_eq (I := I) g x₀

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_center_isInvertible
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)).IsInvertible := by
  rw [metricFlatModelInChart_center_eq (I := I) g x₀]
  exact ContinuousLinearMap.isInvertible_equiv


omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart (I := I) g x₀)
      (Set.range I) (extChartAt I x₀ x₀) := by
  let e := trivializationAt (E →L[Real] E →L[Real] Real)
      (fun p : M => TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real) x₀
  have hg :
      ContMDiffAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real)) ∞
        (fun p : M =>
          (⟨p, g.inner p⟩ :
            TotalSpace (E →L[Real] E →L[Real] Real)
              (fun p : M =>
                TangentSpace I p →L[Real] TangentSpace I p →L[Real] Real)))
        x₀ :=
    (g.contMDiff.contMDiffAt (x := x₀)).of_le (by simp)
  have hcoord :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => (e ⟨p, g.inner p⟩).2) x₀ :=
    by
      rw [contMDiffAt_totalSpace] at hg
      simpa [e] using hg.2
  have hsymm :
      ContMDiffWithinAt 𝓘(Real, E) I ∞ (extChartAt I x₀).symm
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range_self (I := I) (n := ∞) x₀
  have hcenter :
      (extChartAt I x₀).symm (extChartAt I x₀ x₀) = x₀ :=
    (extChartAt I x₀).left_inv (mem_extChartAt_source (I := I) x₀)
  have hcoord_center :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => (e ⟨p, g.inner p⟩).2)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    simpa [hcenter] using hcoord
  have hcomp :
      ContMDiffWithinAt 𝓘(Real, E)
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        ((fun p : M => (e ⟨p, g.inner p⟩).2) ∘ (extChartAt I x₀).symm)
        (Set.range I) (extChartAt I x₀ x₀) :=
    hcoord_center.comp_contMDiffWithinAt
      (x := extChartAt I x₀ x₀) hsymm
  exact hcomp.contDiffWithinAt

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_apply_of_target
    (g : SmoothRiemannianMetric I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) (v w : E) :
    metricFlatModelInChart (I := I) g x₀ y v w =
      g.inner ((extChartAt I x₀).symm y)
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real
          ((extChartAt I x₀).symm y) v)
        ((trivializationAt E (TangentSpace I : M -> Type _) x₀).symmL Real
          ((extChartAt I x₀).symm y) w) := by
  let p : M := (extChartAt I x₀).symm y
  have hp_source : p ∈ (extChartAt I x₀).source := by
    simpa [p] using (extChartAt I x₀).map_target hy
  have hp_frame : p ∈ coordinateFrameSet (I := I) x₀ := by
    simpa [coordinateFrameSet, coordinateTrivializationAt, extChartAt_source] using hp_source
  have hpy : extChartAt I x₀ p = y := by
    simpa [p] using (extChartAt I x₀).right_inv hy
  have hcenter : (extChartAt I x₀).symm (extChartAt I x₀ p) = p :=
    (extChartAt I x₀).left_inv hp_source
  rw [← hpy, hcenter]
  exact Tensor.Coordinates.flatChart_apply (I := I) g x₀ hp_frame v w


omit [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricFlatModelInChart_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        ContinuousLinearMap.inverse
          (metricFlatModelInChart (I := I) g x₀ y))
      (Set.range I) (extChartAt I x₀ x₀) := by
  exact
    (metricFlatModelInChart_center_isInvertible (I := I) g x₀).contDiffAt_map_inverse
      |>.comp_contDiffWithinAt
        (x := extChartAt I x₀ x₀)
        (metricFlatModelInChart_contDiffWithinAt (I := I) g x₀)

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem metricFlatModelInChart_contDiffWithinAt_of_mem
    (g : SmoothRiemannianMetric I M) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt I x₀).target) :
    ContDiffWithinAt Real ∞
      (metricFlatModelInChart (I := I) g x₀)
      (Set.range I) y := by
  let e := trivializationAt E (TangentSpace I : M -> Type _) x₀
  let b := Module.finBasis Real E
  let p : M := (extChartAt I x₀).symm y
  have hp_source : p ∈ (extChartAt I x₀).source := by
    simpa [p] using (extChartAt I x₀).map_target hy
  have hpE : p ∈ e.baseSet := by
    simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp_source
  have hlocal :
      ContMDiffAt I 𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        (fun p : M => localMetricFlatBasis (I := I) e b g p) p :=
    localMetricFlatBasis_contMDiffAt (I := I) e b g hpE
  have hsymm :
      ContMDiffWithinAt 𝓘(Real, E) I ∞ (extChartAt I x₀).symm
        (Set.range I) y := by
    simpa using
      contMDiffWithinAt_extChartAt_symm_range (I := I) (n := ∞) x₀ hy
  have hcomp :
      ContMDiffWithinAt 𝓘(Real, E)
        𝓘(Real, E →L[Real] E →L[Real] Real) ∞
        ((fun p : M => localMetricFlatBasis (I := I) e b g p) ∘
          (extChartAt I x₀).symm)
        (Set.range I) y :=
    hlocal.comp_contMDiffWithinAt (x := y) hsymm
  have heq :
      metricFlatModelInChart (I := I) g x₀ =ᶠ[𝓝[Set.range I] y]
        fun y' : E =>
          localMetricFlatBasis (I := I) e b g ((extChartAt I x₀).symm y') := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem (I := I) hy] with y' hy'
    have hp'_source : (extChartAt I x₀).symm y' ∈ (extChartAt I x₀).source :=
      (extChartAt I x₀).map_target hy'
    have hp'E : (extChartAt I x₀).symm y' ∈ e.baseSet := by
      simpa [e, TangentBundle.trivializationAt_baseSet, extChartAt_source] using hp'_source
    ext v w
    calc
      metricFlatModelInChart (I := I) g x₀ y' v w =
          g.inner ((extChartAt I x₀).symm y')
            (e.symmL Real ((extChartAt I x₀).symm y') v)
            (e.symmL Real ((extChartAt I x₀).symm y') w) := by
            simpa [e] using metricFlatModelInChart_apply_of_target
              (I := I) g x₀ hy' v w
      _ =
          localMetricFlatBasis (I := I) e b g ((extChartAt I x₀).symm y') v w := by
            rw [localMetricFlatBasis_eq_inner (I := I) e b g hp'E v w]
  exact hcomp.contDiffWithinAt.congr_of_eventuallyEq heq
    (heq.self_of_nhdsWithin (extChartAt_target_subset_range x₀ hy))


omit [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricFlatModelInChart_component_contDiffWithinAt
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (k l : CoordinateIdx (𝕜 := Real) E) :
    ContDiffWithinAt Real ∞
      (fun y : E =>
        (Module.finBasis Real E).coord k
          ((ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y))
            (LinearMap.toContinuousLinearMap
              ((Module.finBasis Real E).coord l))))
      (Set.range I) (extChartAt I x₀ x₀) := by
  let εl : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)
  let εk : E →L[Real] Real :=
    LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord k)
  have hinv := inverseMetricFlatModelInChart_contDiffWithinAt (I := I) g x₀
  have happ :
      ContDiffWithinAt Real ∞
        (fun y : E =>
          (ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ y)) εl)
        (Set.range I) (extChartAt I x₀ x₀) := by
    simpa [εl] using hinv.clm_apply contDiffWithinAt_const
  simpa [εk, εl] using (contDiffWithinAt_const (c := εk)).clm_apply happ

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem inverseMetricFlatModelInChart_component_center_eq_symm
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) :
    (Module.finBasis Real E).coord i
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord j))) =
      (Module.finBasis Real E).coord j
        ((ContinuousLinearMap.inverse
            (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
          (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord i))) := by
  simpa only [metricFlatModelInChart,
    Tensor.Coordinates.inverseMetricFlatModelInChartComponent] using
    Tensor.Coordinates.inverseMetricFlatModelInChart_component_center_eq_symm
      (I := I) g x₀ i j

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem inverseMetricFlatModelInChart_metricInverseInBasis_center
    (g : SmoothRiemannianMetric I M) (x₀ : M) :
    MetricInverseInBasis (I := I) g x₀ (coordinateFrameAtToBasis (I := I) x₀)
      (fun k l : CoordinateIdx (𝕜 := Real) E =>
        (Module.finBasis Real E).coord k
          ((ContinuousLinearMap.inverse
              (metricFlatModelInChart (I := I) g x₀ (extChartAt I x₀ x₀)))
            (LinearMap.toContinuousLinearMap ((Module.finBasis Real E).coord l)))) := by
  simpa only [metricFlatModelInChart,
    Tensor.Coordinates.inverseMetricFlatModelInChartComponent] using
    Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := I) g x₀

noncomputable def metricFlatModelInChartComponent
    (g : SmoothRiemannianMetric I M) (x₀ : M)
    (i j : CoordinateIdx (𝕜 := Real) E) (y : E) : Real :=
  metricFlatModelInChart (I := I) g x₀ y
    ((Module.finBasis Real E) i) ((Module.finBasis Real E) j)
end DifferentialGeometry.Geometry.Connection
