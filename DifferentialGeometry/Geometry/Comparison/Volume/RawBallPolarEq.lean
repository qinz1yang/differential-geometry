import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Injectivity
import DifferentialGeometry.Geometry.Exponential.MinimizingDomain.Topology
import DifferentialGeometry.Geometry.Exponential.Radial
import DifferentialGeometry.Geometry.Exponential.CompactBall
import DifferentialGeometry.Geometry.Exponential.VolumeDensity
import DifferentialGeometry.Geometry.Geodesic.Flow.VelocityLift
import DifferentialGeometry.Analysis.Integration.Measure.Chart.HaarBasis
import DifferentialGeometry.Analysis.Integration.Measure.Chart.Density
import DifferentialGeometry.Analysis.Integration.Measure.Parametric.AreaFormula
import DifferentialGeometry.Analysis.Integration.Measure.Polar.Evaluation
import DifferentialGeometry.Analysis.Integration.Measure.Polar.NullSets
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Area
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Basic
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Density
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain.Basic
import DifferentialGeometry.Geometry.Comparison.HopfRinow.RadialSurjectivity
import DifferentialGeometry.Geometry.Geodesic.Maximal.Rescaling
import DifferentialGeometry.Geometry.Geodesic.Equation.ProjectionDerivative

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold MeasureTheory Set
open Filter
open scoped ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

attribute [instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

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

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)] in
private theorem raw_exp_density_local
    (g : SmoothRiemannianMetric I M) (p : M) (v : E)
    (hv : (show TangentSpace I p from v) ∈ expDomain (I := I) g p) :
    paramDensity (I := I) g
        (fun b : E => expMap (I := I) g p
          (show TangentSpace I p from b)) v =
      curveDensity (I := I) g
        (fun t : ℝ => expMap (I := I) g p
          (show TangentSpace I p from t • v))
        (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
          mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
            expMap (I := I) g p
              (show TangentSpace I p from
                t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1 := by
  have hfield :
      (fun i : Fin (Module.finrank ℝ E) =>
        radialJacobiField (I := I) g p v (chartModelBasis E i)) =
      (fun i : Fin (Module.finrank ℝ E) => fun t : ℝ =>
        (mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
          expMap (I := I) g p
            (show TangentSpace I p from
              t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ))) := by
    funext i t
    simpa only [zero_smul, add_zero] using
      (radialJacobiField_eq (I := I) g p v (chartModelBasis E i) t)
  rw [← hfield]
  change paramDensity (I := I) g
      (fun b : E => expMap (I := I) g p
        (show TangentSpace I p from b)) v =
    curveDensity (I := I) g (radialCurve (I := I) g p v)
      (fun i : Fin (Module.finrank ℝ E) =>
        radialJacobiField (I := I) g p v (chartModelBasis E i)) 1
  exact paramDensity_expMap_eq_curveDensity (I := I) g p v hv

private theorem isCompact_rawSeg
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    IsCompact (minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p R) := by
  apply isCompact_minimizingDomain_inter (I := I) g p (isCompact_closedGBall (I := I) g p R)
  intro v hv
  exact mem_expDomain_of_isCompact_closedEBall (I := I) g hEnorm p
    (show TangentSpace I p from v) (lt_of_le_of_lt hv hRR₀) hcpt

omit [NeZero (Module.finrank ℝ E)] in
private theorem rawSegInt_image_eq
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (R : ℝ) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((fun v : E => expMap (I := I) g p
          (show TangentSpace I p from v)) ''
          (extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R)) =
      ∫⁻ v in extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (fun t : ℝ => expMap (I := I) g p
              (show TangentSpace I p from t • v))
            (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
              mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
                expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
        ∂(modelHaar (E := E)) := by
  let K : Set E := extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R
  let F : E → M := fun v => expMap (I := I) g p
    (show TangentSpace I p from v)
  let U : Set E := {v : E | (show TangentSpace I p from v) ∈
    expDomain (I := I) g p}
  have hK : MeasurableSet K := by
    simpa only [K] using ((measurableSet_extendibleMinimizingDomain (I := I) g hEnorm p).inter
      (measurableSet_gBall (I := I) g p R))
  have hKdom : K ⊆ expDomain (I := I) g p := by
    intro v hv
    change v ∈ extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R at hv
    exact minimizingDomain_subset_expDomain (I := I) g p
      (extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hv.1)
  have hU : IsOpen U := by
    exact isOpen_expDomain (I := I) g p
  have hKU : K ⊆ U := by
    intro v hv
    change (show TangentSpace I p from v) ∈ expDomain (I := I) g p
    exact hKdom hv
  have hF : ContMDiffOn 𝓘(ℝ, E) I 1 F U := by
    change ContMDiffOn 𝓘(ℝ, E) I 1 F (expDomain (I := I) g p)
    simpa only [F] using
      (contMDiffOn_expMap (I := I) g p).of_le (by norm_num)
  have hinj : Set.InjOn F K := by
    simpa only [F, K] using
      (injOn_expMap_extendibleMinimizingDomain (I := I) g hEnorm p).mono Set.inter_subset_left
  have hcov := riemannianVolumeMeasure_image_eq (I := I) g (f := F) (U := U)
    hU hK hKU hF hinj
  have hjac : ∀ v ∈ K,
      paramDensity (I := I) g F v =
        curveDensity (I := I) g
          (fun t : ℝ => expMap (I := I) g p
            (show TangentSpace I p from t • v))
          (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
            mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
            expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1 := by
    intro v hv
    simpa only [F] using raw_exp_density_local (I := I) g p v (hKdom hv)
  have hint :
      (∫⁻ v in K, ENNReal.ofReal (paramDensity (I := I) g F v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in K, ENNReal.ofReal
          (curveDensity (I := I) g
            (fun t : ℝ => expMap (I := I) g p
              (show TangentSpace I p from t • v))
            (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
              mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
                expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
          ∂(modelHaar (E := E)) := by
    refine setLIntegral_congr_fun hK (fun v hv => ?_)
    exact congrArg ENNReal.ofReal (hjac v hv)
  simpa only [F, K] using hcov.trans hint

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] in
private theorem rawSegEnd_ray_sub
    (g : SmoothRiemannianMetric I M) (p : M) (u : E) :
    ({r : Ioi (0 : ℝ) |
      r.1 • u ∈ minimizingDomain (I := I) g p \ extendibleMinimizingDomain (I := I) g p} :
      Set (Ioi (0 : ℝ))).Subsingleton := by
  rintro ⟨a, ha0⟩ ⟨haD, haI⟩ ⟨b, hb0⟩ ⟨hbD, hbI⟩
  have ha_pos : 0 < a := ha0
  have hb_pos : 0 < b := hb0
  apply Subtype.ext
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    apply haI
    refine ⟨b / a, (one_lt_div ha_pos).2 hab, ?_⟩
    rw [smul_smul, div_mul_cancel₀ b ha_pos.ne']
    exact hbD
  · exact hab
  · exfalso
    apply hbI
    refine ⟨a / b, (one_lt_div hb_pos).2 hab, ?_⟩
    rw [smul_smul, div_mul_cancel₀ a hb_pos.ne']
    exact haD

theorem rawSegEnd_null
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    (modelHaar (E := E))
        ((minimizingDomain (I := I) g p \ extendibleMinimizingDomain (I := I) g p) ∩
          closedGBall (I := I) g p R) = 0 := by
  let _ : Measure.IsAddHaarMeasure (modelHaar (E := E)) := modelHaar_isAddHaarMeasure
  let K : Set E := minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p R
  have hK : IsCompact K := isCompact_rawSeg (I := I) g hEnorm p hRR₀ hcpt
  apply measure_mono_null ?_ (hK.measure_setOf_forall_smul_notMem (modelHaar (E := E)))
  rintro v ⟨⟨hv, hvnot⟩, hvball⟩
  refine ⟨⟨hv, hvball⟩, ?_⟩
  intro c hc hcv
  exact hvnot ⟨c, hc, hcv.1⟩

private theorem rawSegEnd_nullMeas
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    NullMeasurableSet
      ((minimizingDomain (I := I) g p \ extendibleMinimizingDomain (I := I) g p) ∩
        closedGBall (I := I) g p R)
      (modelHaar (E := E)) :=
  NullMeasurableSet.of_null (rawSegEnd_null (I := I) g hEnorm p hRR₀ hcpt)

omit [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
private theorem gSphere_null
    (g : SmoothRiemannianMetric I M) (p : M) (R : ℝ) :
    (modelHaar (E := E))
        {v : E | Real.sqrt
          (g.inner p (show TangentSpace I p from v)
            (show TangentSpace I p from v)) = R} = 0 := by
  classical
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let q : E → ℝ := fun v => Real.sqrt
    (g.inner p (show TangentSpace I p from v)
      (show TangentSpace I p from v))
  let level : Set E := {v | q v = R}
  have hq_cont : Continuous q := by
    exact Real.continuous_sqrt.comp
      (by
        change Continuous (fun v : TangentSpace I p => g.inner p v v)
        exact continuous_gInner_self (I := I) g p)
  have hlevel_meas : MeasurableSet level :=
    (isClosed_eq hq_cont continuous_const).measurableSet
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g p
  have hlevel_eq : level = L '' Metric.sphere (0 : E) R := by
    ext v
    constructor
    · intro hv
      refine ⟨L.symm v, ?_, L.apply_symm_apply v⟩
      rw [mem_sphere_zero_iff_norm]
      have hqv : q v = R := hv
      have hsqrt : q v = ‖L.symm v‖ := by
        have hs := normalFrame_sqrt (I := I) g p (L.symm v)
        change q (L (L.symm v)) = ‖L.symm v‖ at hs
        simpa only [L.apply_symm_apply] using hs
      exact hsqrt.symm.trans hqv
    · rintro ⟨w, hw, rfl⟩
      have hnorm : ‖w‖ = R := by
        simpa only [mem_sphere_zero_iff_norm] using hw
      change q (L w) = R
      have hs := normalFrame_sqrt (I := I) g p w
      change q (L w) = ‖w‖ at hs
      exact hs.trans hnorm
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  let b' : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    b.map L.toLinearEquiv
  have hmap : Measure.map L (modelHaar (E := E)) = b'.addHaar := by
    simpa only [b, b', modelHaar] using Module.Basis.map_addHaar b L
  have hlevel_map : b'.addHaar level = 0 := by
    rw [← hmap, Measure.map_apply_of_aemeasurable
      L.continuous.measurable.aemeasurable hlevel_meas, hlevel_eq,
      L.injective.preimage_image]
    exact Measure.addHaar_sphere (modelHaar (E := E)) (0 : E) R
  have hlevel_zero : (modelHaar (E := E)) level = 0 := by
    change b.addHaar level = 0
    rw [← Module.Basis.det_smul_addHaar b b', Measure.smul_apply,
      hlevel_map, smul_zero]
  simpa only [level, q] using hlevel_zero

omit [NeZero (Module.finrank ℝ E)]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] in
private theorem riemVol_rawExp_le
    (g : SmoothRiemannianMetric I M) (p : M) {K : Set E}
    (hK : IsCompact K)
    (hKdom : K ⊆ expDomain (I := I) g p) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((fun v : E => expMap (I := I) g p
          (show TangentSpace I p from v)) '' K) ≤
      ∫⁻ v in K, ENNReal.ofReal
        (paramDensity (I := I) g
          (fun v : E => expMap (I := I) g p
            (show TangentSpace I p from v)) v)
        ∂(modelHaar (E := E)) := by
  let U : Set E := {v : E | (show TangentSpace I p from v) ∈
    expDomain (I := I) g p}
  let F : E → M := fun v => expMap (I := I) g p
    (show TangentSpace I p from v)
  have hU : IsOpen U := by
    exact isOpen_expDomain (I := I) g p
  have hKU : K ⊆ U := by
    intro v hv
    exact hKdom hv
  have hF : ContMDiffOn 𝓘(ℝ, E) I 1 F U := by
    change ContMDiffOn 𝓘(ℝ, E) I 1 F (expDomain (I := I) g p)
    simpa only [F] using
      (contMDiffOn_expMap (I := I) g p).of_le (by norm_num)
  simpa only [F] using
    riemannianVolumeMeasure_image_le_of_isCompact (I := I) g hU hK hKU hF

private theorem ball_sub_rawSeg
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R ≤ R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    {q : M | riemannianEDist I p q < ENNReal.ofReal R} ⊆
      (fun v : E => expMap (I := I) g p
        (show TangentSpace I p from v)) ''
        (minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p R) := by
  intro q hq
  have hqR₀ : riemannianEDist I p q < ENNReal.ofReal R₀ :=
    hq.trans_le (ENNReal.ofReal_mono hRR₀)
  obtain ⟨v, _hvdom, hvexp, hvlen⟩ :=
    RadialSurjectivity.minExp_of_cptBall (I := I) g hEnorm p q hqR₀ hcpt
  refine ⟨v, ⟨?_, ?_⟩, hvexp⟩
  · subst q
    exact hvlen
  · change Real.sqrt (g.inner p v v) ≤ R
    exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
      (Real.sqrt_nonneg _)).mp (hvlen.trans_lt hq))

theorem rawBall_integral_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R R₀ : ℝ} (hRR₀ : R < R₀)
    (hcpt : @IsCompact M PseudoEMetricSpace.toUniformSpace.toTopologicalSpace
      (Metric.closedEBall p (ENNReal.ofReal R₀))) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {q : M | riemannianEDist I p q < ENNReal.ofReal R} =
      ∫⁻ v in extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (fun t : ℝ => expMap (I := I) g p
              (show TangentSpace I p from t • v))
            (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
              mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
                expMap (I := I) g p
                  (show TangentSpace I p from
                    t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
        ∂(modelHaar (E := E)) := by
  classical
  let B : Set M := {q : M | riemannianEDist I p q < ENNReal.ofReal R}
  let K : Set E := extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R
  let L : Set E := minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p R
  let F : E → M := fun v => expMap (I := I) g p
    (show TangentSpace I p from v)
  let D : E → ENNReal := fun v => ENNReal.ofReal
    (curveDensity (I := I) g
      (fun t : ℝ => expMap (I := I) g p
        (show TangentSpace I p from t • v))
      (fun (i : Fin (Module.finrank ℝ E)) (t : ℝ) =>
        mfderiv 𝓘(ℝ, ℝ) I (fun s : ℝ =>
          expMap (I := I) g p
            (show TangentSpace I p from
              t • (v + s • (chartModelBasis E) i))) 0 (1 : ℝ)) 1)
  have hL : IsCompact L := by
    simpa only [L] using isCompact_rawSeg (I := I) g hEnorm p hRR₀ hcpt
  have hLdom : L ⊆ expDomain (I := I) g p := by
    intro v hv
    change v ∈ minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p R at hv
    exact minimizingDomain_subset_expDomain (I := I) g p hv.1
  have hKsubL : K ⊆ L := by
    intro v hv
    change v ∈ extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R at hv
    refine ⟨extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hv.1, ?_⟩
    change Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)) ≤ R
    have hvball := hv.2
    change Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)) < R at hvball
    exact le_of_lt hvball
  have hdiff_sub :
      L \ K ⊆
        ((minimizingDomain (I := I) g p \ extendibleMinimizingDomain (I := I) g p) ∩
          closedGBall (I := I) g p R) ∪
          {v : E | Real.sqrt
            (g.inner p (show TangentSpace I p from v)
              (show TangentSpace I p from v)) = R} := by
    rintro v ⟨hvL, hvK⟩
    change v ∈ minimizingDomain (I := I) g p ∩ closedGBall (I := I) g p R at hvL
    change v ∉ extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R at hvK
    rcases hvL with ⟨hvraw, hvclosed⟩
    by_cases hvint : v ∈ extendibleMinimizingDomain (I := I) g p
    · right
      change Real.sqrt
        (g.inner p (show TangentSpace I p from v)
          (show TangentSpace I p from v)) = R
      apply le_antisymm hvclosed
      apply le_of_not_gt
      intro hvball
      apply hvK
      exact ⟨hvint, hvball⟩
    · left
      exact ⟨⟨hvraw, hvint⟩, hvclosed⟩
  have hdiff : (modelHaar (E := E)) (L \ K) = 0 := by
    apply measure_mono_null hdiff_sub
    apply measure_union_null
    · simpa only [L] using rawSegEnd_null (I := I) g hEnorm p hRR₀ hcpt
    · exact gSphere_null (I := I) (E := E) g p R
  have hLKae : L =ᵐ[modelHaar (E := E)] K := by
    rw [ae_eq_set]
    refine ⟨hdiff, ?_⟩
    rw [sdiff_eq_empty.mpr hKsubL, measure_empty]
  have hInt : (∫⁻ v in L, D v ∂(modelHaar (E := E))) =
      ∫⁻ v in K, D v ∂(modelHaar (E := E)) :=
    setLIntegral_congr hLKae
  have hcover : B ⊆ F '' L := by
    simpa only [B, F, L] using
      ball_sub_rawSeg (I := I) g hEnorm p hRR₀.le hcpt
  have hupper : riemannianVolumeMeasure (I := I) (M := M) g B ≤
      ∫⁻ v in K, D v ∂(modelHaar (E := E)) := by
    calc
      riemannianVolumeMeasure (I := I) (M := M) g B ≤
          riemannianVolumeMeasure (I := I) (M := M) g (F '' L) :=
        measure_mono hcover
      _ ≤ ∫⁻ v in L, D v ∂(modelHaar (E := E)) := by
        have hparam :
            riemannianVolumeMeasure (I := I) (M := M) g (F '' L) ≤
              ∫⁻ v in L, ENNReal.ofReal (paramDensity (I := I) g
                (fun v : E => expMap (I := I) g p
                  (show TangentSpace I p from v)) v)
                ∂(modelHaar (E := E)) := by
          simpa only [F] using riemVol_rawExp_le (I := I) g p hL hLdom
        have hreplace :
            (∫⁻ v in L, ENNReal.ofReal (paramDensity (I := I) g
                (fun v : E => expMap (I := I) g p
                  (show TangentSpace I p from v)) v)
                ∂(modelHaar (E := E))) =
              ∫⁻ v in L, D v ∂(modelHaar (E := E)) := by
          refine setLIntegral_congr_fun hL.measurableSet (fun v hv => ?_)
          exact congrArg ENNReal.ofReal
            (by simpa only [F, D] using
              raw_exp_density_local (I := I) g p v (hLdom hv))
        exact hparam.trans_eq hreplace
      _ = ∫⁻ v in K, D v ∂(modelHaar (E := E)) := hInt
  have hFKsub : F '' K ⊆ B := by
    rintro q ⟨v, hvK, rfl⟩
    change v ∈ extendibleMinimizingDomain (I := I) g p ∩ gBall (I := I) g p R at hvK
    change riemannianEDist I p
      (expMap (I := I) g p (show TangentSpace I p from v)) < ENNReal.ofReal R
    have hvraw : v ∈ minimizingDomain (I := I) g p :=
      extendibleMinimizingDomain_subset_minimizingDomain (I := I) g hEnorm p hvK.1
    change ENNReal.ofReal
      (Real.sqrt (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v))) =
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from v)) at hvraw
    rw [← hvraw]
    have hvball := hvK.2
    change Real.sqrt
      (g.inner p (show TangentSpace I p from v)
        (show TangentSpace I p from v)) < R at hvball
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (Real.sqrt_nonneg _)).mpr hvball
  have himage : riemannianVolumeMeasure (I := I) (M := M) g (F '' K) =
      ∫⁻ v in K, D v ∂(modelHaar (E := E)) := by
    simpa only [F, K, D] using
      rawSegInt_image_eq (I := I) g hEnorm p R
  apply le_antisymm hupper
  calc
    ∫⁻ v in K, D v ∂(modelHaar (E := E)) =
        riemannianVolumeMeasure (I := I) (M := M) g (F '' K) := himage.symm
    _ ≤ riemannianVolumeMeasure (I := I) (M := M) g B := measure_mono hFKsub

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
