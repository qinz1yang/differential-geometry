import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.CompactBall
import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Injectivity
import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Measure
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaFormula
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Integration
import DifferentialGeometry.Analysis.Integration.Measure.Polar.Evaluation

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open Exponential NormalCoordinates Variation
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

theorem riemannianVolumeMeasure_ball_eq_lintegral_curveDensity_euclideanNormalFrame
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (R : ℝ)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {q : M | riemannianEDist I p q < ENNReal.ofReal R} =
      ∫⁻ w in (NormalCoordinates.euclideanNormalFrame (I := I) g p) ⁻¹'
          (show Set E from extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R),
        ENNReal.ofReal (Variation.curveDensity (I := I) g
          (radialCurve (I := I) g p (NormalCoordinates.euclideanNormalFrame (I := I) g p w))
          (fun i => radialJacobiField (I := I) g p
            (NormalCoordinates.euclideanNormalFrame (I := I) g p w)
            (NormalCoordinates.normalBasis (I := I) g p i)) 1)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))) := by
  rw [riemannianVolumeMeasure_ball_eq_lintegral_paramDensity_expMap g hEnorm p R hcpt]
  apply lintegral_paramDensity_expMap_eq_lintegral_curveDensity_euclideanNormalFrame
  · exact (measurableSet_extendibleMinimizingDomain (I := I) g hEnorm p).inter
      (measurableSet_gBall (I := I) g p R)
  · intro v hv
    exact minimizingDomain_subset_expDomain (I := I) g p
      (extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hv.1)

local notation "F₀" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

theorem riemannianVolumeMeasure_ball_eq_lintegral_polar_euclideanNormalFrame
    [Nontrivial E] [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {t A : ℝ} (htA : t ≤ A)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal A))) :
    let L : F₀ → E := fun w => euclideanNormalFrame (I := I) g p w
    let D : F₀ → ℝ≥0∞ := fun w => ENNReal.ofReal
      (curveDensity (I := I) g (radialCurve (I := I) g p (L w))
        (fun i => radialJacobiField (I := I) g p (L w) (normalBasis (I := I) g p i)) 1)
    let T : Set F₀ := L ⁻¹'
      (extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p A)
    riemannianVolumeMeasure (I := I) (M := M) g
        {q : M | riemannianEDist I p q < ENNReal.ofReal t} =
      ∫⁻ u : Metric.sphere (0 : F₀) 1,
        ∫⁻ r : Ioi (0 : ℝ) in {r : Ioi (0 : ℝ) | r.1 < t},
          T.indicator D (r.1 • u.1)
          ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1)
        ∂(volume : Measure F₀).toSphere := by
  let L : F₀ → E := fun w => euclideanNormalFrame (I := I) g p w
  let D : F₀ → ℝ≥0∞ := fun w => ENNReal.ofReal
    (curveDensity (I := I) g (radialCurve (I := I) g p (L w))
      (fun i => radialJacobiField (I := I) g p (L w) (normalBasis (I := I) g p i)) 1)
  let T : Set F₀ := L ⁻¹'
    (extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p A)
  have hL : Continuous L := (euclideanNormalFrame (I := I) g p).continuous
  have hT : MeasurableSet T :=
    ((measurableSet_extendibleMinimizingDomain (I := I) g hEnorm p).inter
      (measurableSet_gBall (I := I) g p A)).preimage hL.measurable
  have hTD : MapsTo L T (expDomain (I := I) g p) := by
    intro w hw
    exact minimizingDomain_subset_expDomain (I := I) g p
      (extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hw.1)
  have hD : AEMeasurable D ((volume : Measure F₀).restrict (T ∩ Metric.ball 0 t)) := by
    apply ENNReal.measurable_ofReal.comp_aemeasurable
    exact (((continuousOn_curveDensity_radialJacobiField_basis (I := I) g p
      (normalBasis (I := I) g p)).comp hL.continuousOn hTD).mono
        inter_subset_left).aemeasurable (hT.inter measurableSet_ball)
  have hball (r : ℝ) : L ⁻¹' (show Set E from gBall (I := I) g p r) =
      Metric.ball (0 : F₀) r := by
    ext w
    change Real.sqrt (g.inner p (euclideanNormalFrame (I := I) g p w)
      (euclideanNormalFrame (I := I) g p w)) < r ↔ dist w 0 < r
    rw [euclideanNormalFrame_sqrt, dist_zero_right]
  have hpre : L ⁻¹' (extendibleMinimizingDomain (I := I) g p ∩
      (show Set E from gBall (I := I) g p t)) = T ∩ Metric.ball (0 : F₀) t := by
    change (L ⁻¹' extendibleMinimizingDomain (I := I) g p) ∩
      (L ⁻¹' (show Set E from gBall (I := I) g p t)) =
        ((L ⁻¹' extendibleMinimizingDomain (I := I) g p) ∩
          (L ⁻¹' (show Set E from gBall (I := I) g p A))) ∩ Metric.ball (0 : F₀) t
    rw [hball t, hball A, inter_assoc,
      inter_eq_right.mpr (Metric.ball_subset_ball htA)]
  have hcptt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal t)) := by
    let : TopologicalSpace M := PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
    exact hcpt.of_isClosed_subset Metric.isClosed_closedEBall
      (Metric.closedEBall_subset_closedEBall (ENNReal.ofReal_mono htA))
  have hdim : Module.finrank ℝ F₀ = Module.finrank ℝ E := by simp
  let _ : Nontrivial F₀ :=
    Module.nontrivial_of_finrank_pos (hdim.symm ▸ Module.finrank_pos (R := ℝ) (M := E))
  change riemannianVolumeMeasure (I := I) (M := M) g
    {q : M | riemannianEDist I p q < ENNReal.ofReal t} = _
  calc
    _ = ∫⁻ w in L ⁻¹' (extendibleMinimizingDomain (I := I) g p ∩
        (show Set E from gBall (I := I) g p t)), D w ∂(volume : Measure F₀) :=
      riemannianVolumeMeasure_ball_eq_lintegral_curveDensity_euclideanNormalFrame
        (I := I) g hEnorm p t hcptt
    _ = ∫⁻ w in T ∩ Metric.ball (0 : F₀) t, D w ∂(volume : Measure F₀) := by rw [hpre]
    _ = _ := by
      simpa only [hdim] using
        setLIntegral_inter_ball_polar (volume : Measure F₀) T hT t D hD


end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
