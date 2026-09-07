import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.CompactBall
import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Injectivity
import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Measure
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaFormula

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open Exponential
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance tangentSpaceNormedAddCommGroup
    (x : M) : NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace
    (x : M) : InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace
    (x : M) : NormedSpace ℝ (TangentSpace I x) := inferInstance

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem riemannianVolumeMeasure_ball_eq_lintegral_paramDensity_expMap
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (R : ℝ)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {q : M | riemannianEDist I p q < ENNReal.ofReal R} =
      ∫⁻ v in extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R,
        ENNReal.ofReal (paramDensity (I := I) g
          (fun v : E => expMap (I := I) g p (show TangentSpace I p from v)) v)
        ∂(modelHaar (E := E)) := by
  let B : Set M := {q : M | riemannianEDist I p q < ENNReal.ofReal R}
  let K : Set E := extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R
  let L : Set E := minimizingDomain (I := I) g p ∩ gBall (I := I) g p R
  let F : E → M := fun v => expMap (I := I) g p (show TangentSpace I p from v)
  let U : Set E := expDomain (I := I) g p
  let D : E → ENNReal := fun v => ENNReal.ofReal (paramDensity (I := I) g F v)
  have hL : MeasurableSet L :=
    (measurableSet_minimizingDomain (I := I) g p).inter
      (measurableSet_gBall (I := I) g p R)
  have hK : MeasurableSet K :=
    (measurableSet_extendibleMinimizingDomain (I := I) g hEnorm p).inter
      (measurableSet_gBall (I := I) g p R)
  have hLU : L ⊆ U := fun _ hv => minimizingDomain_subset_expDomain (I := I) g p hv.1
  have hKL : K ⊆ L := fun _ hv =>
    ⟨extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hv.1, hv.2⟩
  have hdiff : (modelHaar (E := E)) (L \ K) = 0 := by
    let _ : Measure.IsAddHaarMeasure (modelHaar (E := E)) := modelHaar_isAddHaarMeasure
    apply measure_mono_null ?_
      (measure_minimizingDomain_sdiff_extendibleMinimizingDomain
        (I := I) g p (modelHaar (E := E)))
    rintro v ⟨hvL, hvK⟩
    exact ⟨hvL.1, fun hvext => hvK ⟨hvext, hvL.2⟩⟩
  have hae : L =ᵐ[modelHaar (E := E)] K := by
    rw [ae_eq_set]
    refine ⟨hdiff, ?_⟩
    rw [sdiff_eq_empty.mpr hKL, measure_empty]
  have hF : ContMDiffOn 𝓘(ℝ, E) I 1 F U :=
    (contMDiffOn_expMap (I := I) g p).of_le (by norm_num)
  have hU : IsOpen U := isOpen_expDomain (I := I) g p
  have hFL : F '' L = B := image_expMap_minimizingDomain_inter_gBall (I := I)
    g hEnorm p R hcpt
  have hB : MeasurableSet B := by
    change MeasurableSet {q : M | riemannianEDist I p q < ENNReal.ofReal R}
    have hdist : Continuous (fun q : M => riemannianEDist I p q) :=
      (continuous_riemannianEDist_to (I := I) p).congr
        (fun _ => Manifold.riemannianEDist_comm)
    exact (isOpen_lt hdist continuous_const).measurableSet
  have hupper : riemannianVolumeMeasure (I := I) (M := M) g B ≤
      ∫⁻ v in K, D v ∂(modelHaar (E := E)) := by
    calc
      riemannianVolumeMeasure (I := I) (M := M) g B =
          riemannianVolumeMeasure (I := I) (M := M) g (F '' L) := by rw [hFL]
      _ ≤ ∫⁻ v in L, D v ∂(modelHaar (E := E)) :=
        riemannianVolumeMeasure_image_le (I := I) g hU hL hLU hF (hFL.symm ▸ hB)
      _ = ∫⁻ v in K, D v ∂(modelHaar (E := E)) := setLIntegral_congr hae
  have hFK : riemannianVolumeMeasure (I := I) (M := M) g (F '' K) =
      ∫⁻ v in K, D v ∂(modelHaar (E := E)) :=
    riemannianVolumeMeasure_image_eq (I := I) g hU hK (hKL.trans hLU) hF
      ((injOn_expMap_extendibleMinimizingDomain (I := I) g hEnorm p).mono inter_subset_left)
  apply le_antisymm hupper
  calc
    ∫⁻ v in K, D v ∂(modelHaar (E := E)) =
        riemannianVolumeMeasure (I := I) (M := M) g (F '' K) := hFK.symm
    _ ≤ riemannianVolumeMeasure (I := I) (M := M) g B :=
      measure_mono (hFL ▸ image_mono hKL)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
