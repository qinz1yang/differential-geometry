import DifferentialGeometry.Geometry.Hyperbolic.CuspMetric
import DifferentialGeometry.Geometry.Measure.ExponentialWarpedEnd
import DifferentialGeometry.Geometry.Measure.ProductMetric
import DifferentialGeometry.Geometry.Metric.WarpedProduct.ExponentialProduct
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.EuclideanHalfSpace
import DifferentialGeometry.Analysis.Integration.Measure.ExponentialTail

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set MeasureTheory Module
open scoped Manifold ContDiff ENNReal Matrix
open DifferentialGeometry DifferentialGeometry.Tensor.Coordinates

open GC.Endpoint DifferentialGeometry.Integral.Measure

namespace DifferentialGeometry.Geometry.Hyperbolic

private local instance : MeasurableSpace Torus := borel Torus
private local instance : BorelSpace Torus := ⟨rfl⟩
private local instance : MeasurableSpace (EuclideanHalfSpace 1) := borel (EuclideanHalfSpace 1)
private local instance : BorelSpace (EuclideanHalfSpace 1) := ⟨rfl⟩

private theorem withDensity_prod_snd_apply_prod {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    [SFinite ν] (f : B → ℝ≥0∞) (hf : Measurable f)
    (s : Set A) (t : Set B) (ht : MeasurableSet t) :
    (μ.prod ν).withDensity (fun p => f p.2) (s ×ˢ t) =
      μ s * ∫⁻ y in t, f y ∂ν := by
  rw [← prod_withDensity_right hf, Measure.prod_prod, withDensity_apply f ht]

private theorem cast_withDensity_apply {A : Type*} {m₁ m₂ : MeasurableSpace A}
    (hm : m₁ = m₂) (μ : @Measure A m₁) (f : A → ℝ≥0∞) (s : Set A) :
    (@Measure.withDensity A m₂
      (cast (congrArg (fun m : MeasurableSpace A => @Measure A m) hm) μ) f) s =
      (@Measure.withDensity A m₁ μ f) s := by
  cases hm
  rfl

private theorem halfLine_exp_tail {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ r : EuclideanHalfSpace 1 in {r | a < r.val 0},
      ENNReal.ofReal (Real.exp (-r.val 0))
      ∂riemannianVolumeMeasure (𝓡∂ 1) (EuclideanHalfSpace 1) (euclideanHalfSpaceMetric 1)) =
      ENNReal.ofReal (Real.exp (-a)) := by
  have hd : Measurable (fun r : EuclideanHalfSpace 1 => r.val 0) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.comp
      continuous_subtype_val).borel_measurable
  have hf : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-r))) := by
    fun_prop
  have ht := setLIntegral_map (μ := riemannianVolumeMeasure (𝓡∂ 1)
      (EuclideanHalfSpace 1) (euclideanHalfSpaceMetric 1))
    (s := Ioi a) measurableSet_Ioi hf hd
  rw [map_riemannianVolumeMeasure_halfLine_depth] at ht
  exact ht.symm.trans (lintegral_exp_neg_halfLine_tail ha)

private theorem halfLine_exp_closed_tail {a : ℝ} (ha : 0 ≤ a) :
    (∫⁻ r : EuclideanHalfSpace 1 in {r | a ≤ r.val 0},
      ENNReal.ofReal (Real.exp (-r.val 0))
      ∂riemannianVolumeMeasure (𝓡∂ 1) (EuclideanHalfSpace 1) (euclideanHalfSpaceMetric 1)) =
      ENNReal.ofReal (Real.exp (-a)) := by
  have hd : Measurable (fun r : EuclideanHalfSpace 1 => r.val 0) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.comp
      continuous_subtype_val).borel_measurable
  have hf : Measurable (fun r : ℝ => ENNReal.ofReal (Real.exp (-r))) := by
    fun_prop
  have ht := setLIntegral_map (μ := riemannianVolumeMeasure (𝓡∂ 1)
      (EuclideanHalfSpace 1) (euclideanHalfSpaceMetric 1))
    (s := Ici a) measurableSet_Ici hf hd
  rw [map_riemannianVolumeMeasure_halfLine_depth] at ht
  exact ht.symm.trans (lintegral_exp_neg_halfLine_closed_tail ha)

private theorem cusp_volume_depth_set (H : HyperbolicCusp)
    (t : Set (EuclideanHalfSpace 1)) (ht : MeasurableSet t) :
    riemannianVolumeMeasure halfCollarModel CuspHalfSpace H.metric {p | p.2 ∈ t} =
      riemannianVolumeMeasure torusModel Torus H.torusMetric Set.univ *
        ∫⁻ r in t, ENNReal.ofReal (Real.exp (-r.val 0))
          ∂riemannianVolumeMeasure (𝓡∂ 1) (EuclideanHalfSpace 1)
            (euclideanHalfSpaceMetric 1) := by
  let μ := riemannianVolumeMeasure torusModel Torus H.torusMetric
  let ν := riemannianVolumeMeasure (𝓡∂ 1) (EuclideanHalfSpace 1) (euclideanHalfSpaceMetric 1)
  let : SigmaFinite ν := riemannianVolumeMeasure_sigmaFinite (euclideanHalfSpaceMetric 1)
  let f : EuclideanHalfSpace 1 → ℝ≥0∞ := fun r => ENNReal.ofReal (Real.exp (-r.val 0))
  have hd : Measurable (fun r : EuclideanHalfSpace 1 => r.val 0) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.comp
      continuous_subtype_val).borel_measurable
  have hf : Measurable f := ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp hd.neg)
  have hm : @Prod.instMeasurableSpace Torus (EuclideanHalfSpace 1)
      (borel Torus) (borel (EuclideanHalfSpace 1)) = borel CuspHalfSpace :=
    @BorelSpace.measurable_eq CuspHalfSpace _
      (@Prod.instMeasurableSpace Torus (EuclideanHalfSpace 1)
        (borel Torus) (borel (EuclideanHalfSpace 1))) inferInstance
  have hp : riemannianVolumeMeasure halfCollarModel CuspHalfSpace
      (H.torusMetric.exponentialWarpedEnd 0) =
      cast (congrArg (fun m : MeasurableSpace CuspHalfSpace => @Measure CuspHalfSpace m) hm)
        (μ.prod ν) := by
    rw [SmoothRiemannianMetric.exponentialWarpedEnd_zero_eq_prod]
    exact riemannianVolumeMeasure_prod H.torusMetric (euclideanHalfSpaceMetric 1)
  have hv := riemannianVolumeMeasure_exponentialWarpedEnd H.torusMetric (1 / 2 : ℝ)
  norm_num [Module.finrank_prod] at hv
  have hmetric : riemannianVolumeMeasure halfCollarModel CuspHalfSpace H.metric =
      (riemannianVolumeMeasure halfCollarModel CuspHalfSpace
        (H.torusMetric.exponentialWarpedEnd 0)).withDensity (fun p => f p.2) := by
    rw [H.metric_eq_exponentialWarpedEnd]
    exact hv
  have htail : ({p : CuspHalfSpace | p.2 ∈ t}) = Set.univ ×ˢ t := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
  rw [hmetric, hp, cast_withDensity_apply hm, htail,
    withDensity_prod_snd_apply_prod μ ν f hf Set.univ t ht]

theorem HyperbolicCusp.volume_tail (H : HyperbolicCusp) {a : ℝ} (ha : 0 ≤ a) :
    riemannianVolumeMeasure halfCollarModel CuspHalfSpace H.metric
      {p | a < p.2.val 0} =
      riemannianVolumeMeasure torusModel Torus H.torusMetric Set.univ *
        ENNReal.ofReal (Real.exp (-a)) := by
  have hd : Measurable (fun r : EuclideanHalfSpace 1 => r.val 0) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.comp
      continuous_subtype_val).borel_measurable
  change riemannianVolumeMeasure halfCollarModel CuspHalfSpace H.metric
    {p | p.2 ∈ {r : EuclideanHalfSpace 1 | a < r.val 0}} = _
  rw [cusp_volume_depth_set H {r | a < r.val 0}
    (show MeasurableSet {r : EuclideanHalfSpace 1 | a < r.val 0} from
      hd measurableSet_Ioi), halfLine_exp_tail ha]

theorem HyperbolicCusp.volume_closed_tail (H : HyperbolicCusp) {a : ℝ} (ha : 0 ≤ a) :
    riemannianVolumeMeasure halfCollarModel CuspHalfSpace H.metric
      {p | a ≤ p.2.val 0} =
      riemannianVolumeMeasure torusModel Torus H.torusMetric Set.univ *
        ENNReal.ofReal (Real.exp (-a)) := by
  have hd : Measurable (fun r : EuclideanHalfSpace 1 => r.val 0) :=
    ((EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 1)).continuous.comp
      continuous_subtype_val).borel_measurable
  change riemannianVolumeMeasure halfCollarModel CuspHalfSpace H.metric
    {p | p.2 ∈ {r : EuclideanHalfSpace 1 | a ≤ r.val 0}} = _
  rw [cusp_volume_depth_set H {r | a ≤ r.val 0}
    (show MeasurableSet {r : EuclideanHalfSpace 1 | a ≤ r.val 0} from
      hd measurableSet_Ici), halfLine_exp_closed_tail ha]

theorem HyperbolicCusp.volume_univ (H : HyperbolicCusp) :
    riemannianVolumeMeasure halfCollarModel CuspHalfSpace H.metric Set.univ =
      riemannianVolumeMeasure torusModel Torus H.torusMetric Set.univ := by
  have h := HyperbolicCusp.volume_closed_tail H (a := 0) le_rfl
  have hs : ({p : CuspHalfSpace | 0 ≤ p.2.val 0}) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro p
    exact p.2.property
  simpa [hs] using h

theorem HyperbolicCusp.volume_isFiniteMeasure (H : HyperbolicCusp) :
    IsFiniteMeasure (riemannianVolumeMeasure halfCollarModel CuspHalfSpace H.metric) := by
  let h := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace H.torusMetric
  refine ⟨?_⟩
  rw [HyperbolicCusp.volume_univ]
  exact measure_lt_top _ _

open Filter
open scoped _root_.Topology

theorem HyperbolicCusp.volume_closed_tail_tendsto_zero (H : HyperbolicCusp) :
    Tendsto (fun a : ℝ =>
      riemannianVolumeMeasure halfCollarModel CuspHalfSpace H.metric
        {p | a ≤ p.2.val 0}) atTop (𝓝 0) := by
  let μ := riemannianVolumeMeasure torusModel Torus H.torusMetric
  let h := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace H.torusMetric
  have hf : Tendsto (fun a : ℝ => ENNReal.ofReal (Real.exp (-a))) atTop (𝓝 0) := by
    convert! (ENNReal.continuous_ofReal.tendsto 0).comp
      Real.tendsto_exp_neg_atTop_nhds_zero using 1
    simp only [ENNReal.ofReal_zero]
  have ht := ENNReal.Tendsto.const_mul hf (Or.inr (measure_ne_top μ Set.univ))
  simp only [mul_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
  exact (HyperbolicCusp.volume_closed_tail H ha).symm

end DifferentialGeometry.Geometry.Hyperbolic
