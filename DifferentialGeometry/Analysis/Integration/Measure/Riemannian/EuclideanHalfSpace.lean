import DifferentialGeometry.Geometry.Metric.EuclideanHalfSpace
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Euclidean
import Mathlib.Dynamics.Ergodic.MeasurePreserving

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set MeasureTheory Module
open scoped Manifold ContDiff ENNReal Matrix
open DifferentialGeometry DifferentialGeometry.Tensor.Coordinates

namespace DifferentialGeometry.Integral.Measure

variable (n : ℕ) [NeZero n]

local notation "Ehs" => EuclideanSpace ℝ (Fin n)
local notation "Hhs" => EuclideanHalfSpace n
local notation "Ihs" => (𝓡∂ n)

private local instance : MeasurableSpace Ehs := borel Ehs
private local instance : BorelSpace Ehs := ⟨rfl⟩
private local instance : MeasurableSpace Hhs := borel Hhs
private local instance : BorelSpace Hhs := ⟨rfl⟩

private theorem halfSpace_chartBasis (α x : Hhs)
    (i : Fin (Module.finrank ℝ Ehs)) :
    chartBasisVecFiber (I := Ihs) α i x = chartModelBasis Ehs i := by
  rw [chartBasisVecFiber,
    TangentBundle.symmL_trivializationAt_eq_core (by
      simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_source, mem_univ]),
    tangentBundleCore_coordChange_model_space]
  rfl

private theorem halfSpace_chartDensity (α x : Hhs) :
    chartDensity (euclideanHalfSpaceMetric n) α x =
      Real.sqrt (Matrix.det (Matrix.of fun i j =>
        inner ℝ (chartModelBasis Ehs i) (chartModelBasis Ehs j))) := by
  unfold chartDensity
  congr 2
  ext i j
  rw [chartGramMatrix_apply]
  erw [euclideanHalfSpaceMetric_inner,
    halfSpace_chartBasis, halfSpace_chartBasis]
  rfl

private theorem halfSpace_chartTarget (α : Hhs) :
    (extChartAt Ihs α).target = Set.range (Ihs : Hhs → Ehs) := by
  rw [extChartAt_target]
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_target,
    preimage_univ, univ_inter]

private theorem halfSpace_chartInverse (α : Hhs) :
    ((extChartAt Ihs α).symm : Ehs → Hhs) = (Ihs).symm := by
  rfl

private def halfSpaceReference : Measure Hhs :=
  Measure.map (Ihs).symm ((volume : Measure Ehs).restrict (Set.range (Ihs : Hhs → Ehs)))

private theorem halfSpace_chartLocal (α : Hhs) :
    chartLocalMeasure (euclideanHalfSpaceMetric n) α = halfSpaceReference n := by
  rw [chartLocalMeasure_def, halfSpace_chartTarget]
  have hdens : (fun y : Ehs => ENNReal.ofReal
      (chartDensity (euclideanHalfSpaceMetric n) α ((extChartAt Ihs α).symm y))) =
      (fun _ : Ehs => ENNReal.ofReal (Real.sqrt (Matrix.det (Matrix.of fun i j =>
        inner ℝ (chartModelBasis Ehs i) (chartModelBasis Ehs j))))) := by
    funext y
    rw [halfSpace_chartDensity]
  rw [hdens, halfSpace_chartInverse, ← restrict_withDensity (Ihs).isClosed_range.measurableSet]
  unfold modelHaar
  rw [addHaar_withDensity_sqrt_det_gramMatrix_eq_volume]
  rfl

private theorem halfSpace_volume :
    riemannianVolumeMeasure Ihs Hhs (euclideanHalfSpaceMetric n) = halfSpaceReference n := by
  classical
  set ρ : SmoothPartitionOfUnity Hhs Ihs Hhs univ := chartAtlasPOU Ihs Hhs with hρ
  set T : Set Hhs := {α : Hhs | (Function.support (ρ α)).Nonempty} with hT
  have hC : Countable T :=
    (countable_nonempty_support_of_pou (I := Ihs) ρ).to_subtype
  rw [riemannianVolumeMeasure_def, riemannianMeasure_eq_sum_support (I := Ihs) _ ρ]
  have hp : (fun α : T => (chartLocalMeasure (I := Ihs) (M := Hhs)
        (euclideanHalfSpaceMetric n) α.val).withDensity
        (fun x => ENNReal.ofReal (ρ α.val x))) =
      (fun α : T => (halfSpaceReference n).withDensity
        (fun x => ENNReal.ofReal (ρ α.val x))) :=
    funext fun α => by rw [halfSpace_chartLocal]
  rw [hp, ← @withDensity_tsum Hhs _ (halfSpaceReference n) T hC
    (fun α : T => fun x : Hhs => ENNReal.ofReal (ρ α.val x))
    (fun α => measurable_ofReal_pou_weight (I := Ihs) ρ α.val)]
  have hsum : (∑' α : T, (fun x : Hhs => ENNReal.ofReal (ρ α.val x))) = 1 := by
    funext x
    rw [ENNReal.tsum_apply]
    have hsupp : Function.support (fun α : Hhs => ENNReal.ofReal (ρ α x)) ⊆ T := by
      intro α hα
      simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le] at hα
      refine Set.nonempty_iff_ne_empty.mpr ?_
      intro hempty
      have hzero : ρ α x = 0 := by
        by_contra hne
        have : x ∈ Function.support (ρ α) := hne
        rw [hempty] at this
        exact this.elim
      linarith
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    exact tsum_ofReal_pou_eq_one (I := Ihs) ρ x
  rw [hsum, withDensity_one]

theorem map_riemannianVolumeMeasure_euclideanHalfSpaceMetric :
    @Measure.map Hhs Ehs (borel Hhs) (borel Ehs) (Subtype.val : Hhs → Ehs)
      (riemannianVolumeMeasure Ihs Hhs (euclideanHalfSpaceMetric n)) =
        (volume : Measure Ehs).restrict {x : Ehs | 0 ≤ x 0} := by
  rw [halfSpace_volume]
  change Measure.map (Ihs : Hhs → Ehs) (Measure.map (Ihs).symm
    ((volume : Measure Ehs).restrict (Set.range (Ihs : Hhs → Ehs)))) = _
  rw [Measure.map_map (Ihs).continuous.measurable (Ihs).continuous_symm.measurable]
  have he : (Ihs ∘ (Ihs).symm : Ehs → Ehs) =ᵐ[(volume : Measure Ehs).restrict (Set.range (Ihs : Hhs → Ehs))] id := by
    filter_upwards [ae_restrict_mem (Ihs).isClosed_range.measurableSet] with x hx
    exact (Ihs).right_inv ((Ihs).target_eq.symm ▸ hx)
  rw [Measure.map_congr he, Measure.map_id]
  congr 1
  change Set.range (Subtype.val : Hhs → Ehs) = {x : Ehs | 0 ≤ x 0}
  exact Subtype.range_coe

private theorem coordinate_volume_preserving :
    MeasurePreserving (fun v : EuclideanSpace ℝ (Fin 1) => v 0)
      (volume : Measure (EuclideanSpace ℝ (Fin 1))) (volume : Measure ℝ) := by
  let e : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ :=
    { (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 => ℝ)).toLinearEquiv with
      norm_map' v := by
        change ‖v 0‖ = ‖v‖
        simp [EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs] }
  exact e.measurePreserving

theorem map_riemannianVolumeMeasure_halfLine_depth :
    Measure.map (fun r : EuclideanHalfSpace 1 => r.val 0)
      (riemannianVolumeMeasure (𝓡∂ 1) (EuclideanHalfSpace 1) (euclideanHalfSpaceMetric 1)) =
        (volume : Measure ℝ).restrict (Set.Ici 0) := by
  have hp := coordinate_volume_preserving
  have hr := hp.restrict_preimage (s := Set.Ici (0 : ℝ)) measurableSet_Ici
  have hi : @Measurable (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin 1))
      (borel (EuclideanHalfSpace 1)) (borel (EuclideanSpace ℝ (Fin 1)))
      (Subtype.val : EuclideanHalfSpace 1 → EuclideanSpace ℝ (Fin 1)) :=
    continuous_subtype_val.borel_measurable
  calc
    _ = Measure.map (fun v : EuclideanSpace ℝ (Fin 1) => v 0)
        (@Measure.map (EuclideanHalfSpace 1) (EuclideanSpace ℝ (Fin 1))
          (borel (EuclideanHalfSpace 1)) (borel (EuclideanSpace ℝ (Fin 1)))
          (Subtype.val : EuclideanHalfSpace 1 → EuclideanSpace ℝ (Fin 1))
          (riemannianVolumeMeasure (𝓡∂ 1) (EuclideanHalfSpace 1) (euclideanHalfSpaceMetric 1))) := by
      rw [Measure.map_map hp.measurable hi]
      rfl
    _ = Measure.map (fun v : EuclideanSpace ℝ (Fin 1) => v 0)
        ((volume : Measure (EuclideanSpace ℝ (Fin 1))).restrict {v | 0 ≤ v 0}) := by
      rw [map_riemannianVolumeMeasure_euclideanHalfSpaceMetric]
    _ = (volume : Measure ℝ).restrict (Set.Ici 0) := hr.map_eq

end DifferentialGeometry.Integral.Measure
