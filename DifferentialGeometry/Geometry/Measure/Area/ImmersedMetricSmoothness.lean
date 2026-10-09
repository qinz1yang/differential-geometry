import DifferentialGeometry.Analysis.Integration.Measure.Parametric.FiniteIntegral
import DifferentialGeometry.Geometry.MinimalSurface.Variation.DiskMetricVariation
import DifferentialGeometry.Geometry.Measure.Area.Pullback
import DifferentialGeometry.Geometry.Measure.Area.Positivity
import DifferentialGeometry.Geometry.Metric.ParameterPullbackFamily
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The area of a fixed immersion on a compact parameter set varies smoothly with the metric.
Only the parameter set is compact; the target manifold may be noncompact. -/
theorem contDiffOn_riemannianArea_metric_of_immersion
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G) {U : ℂ → M} {s K : Set ℂ}
    (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hK : IsCompact K) (hKs : K ⊆ s)
    (hi : ∀ z ∈ K, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    ContDiffOn ℝ ∞ (fun t => riemannianArea (G t) U K) D.regular := by
  let Q : ℝ × ℂ → ℝ := fun p =>
    (G p.1).inner (U p.2) (diskMapPartial U p.2 1) (diskMapPartial U p.2 1) *
      (G p.1).inner (U p.2) (diskMapPartial U p.2 Complex.I)
        (diskMapPartial U p.2 Complex.I) -
      (G p.1).inner (U p.2) (diskMapPartial U p.2 1)
        (diskMapPartial U p.2 Complex.I) ^ 2
  have hpair := contDiffOn_metricFamilyDiskPairing hG D.regular_isOpen
    (Subset.rfl : D.regular ⊆ D.regular) hs hU
  have hQ : ContDiffOn ℝ ∞ Q (D.regular ×ˢ s) :=
    ((hpair 1 1).mul (hpair Complex.I Complex.I)).sub ((hpair 1 Complex.I).pow 2)
  let Ω := (D.regular ×ˢ s) ∩ Q ⁻¹' Ioi 0
  have hΩ : IsOpen Ω :=
    hQ.continuousOn.isOpen_inter_preimage (D.regular_isOpen.prod hs) isOpen_Ioi
  have hsub : D.regular ×ˢ K ⊆ Ω := by
    intro p hp
    refine ⟨⟨hp.1, hKs hp.2⟩, ?_⟩
    exact Real.sqrt_pos.mp (riemannianAreaDensity_pos_of_injective_mfderiv
      (G p.1) (hi p.2 hp.2))
  have hdensity : ContDiffOn ℝ ∞
      (fun p : ℝ × ℂ => riemannianAreaDensity (G p.1) U p.2) Ω := by
    exact (hQ.mono inter_subset_left).sqrt (fun p hp => ne_of_gt hp.2)
  let : MeasureSpace K := MeasureTheory.Measure.Subtype.measureSpace
  let : IsFiniteMeasure (volume : Measure K) := {
    measure_univ_lt_top := by
      rw [MeasureTheory.Measure.Subtype.volume_univ hK.measurableSet.nullMeasurableSet]
      exact hK.measure_lt_top }
  apply (DifferentialGeometry.Integral.Measure.contDiffOn_integral_subtype_of_isCompact
    (⊤ : ℕ∞) hK (volume : Measure K) D.regular_isOpen hΩ hsub hdensity).congr
  intro t _
  exact (integral_subtype hK.measurableSet (riemannianAreaDensity (G t) U)).symm

/-- A smooth immersed disk has smooth area in a smooth family of ambient metrics. -/
theorem SmoothDiskExtension.contDiffOn_area_metric_of_immersion
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G)
    (hi : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    ContDiffOn ℝ ∞ (fun t => riemannianDiskArea (G t) u) D.regular := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
  apply (contDiffOn_riemannianArea_metric_of_immersion hG hs hU
    (isCompact_closedBall (0 : ℂ) 1) hDs hi).congr
  intro t _
  exact riemannianDiskArea_eq_of_extension (G t) u U heq

/-- Ambient isotopy preserves smoothness in time of the area of an immersed disk. -/
theorem SmoothDiskExtension.contDiffOn_area_isotopy_of_immersion [T2Space M]
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G)
    {Φ : ℝ → M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M} {T : Set ℝ}
    (hT : IsOpen T)
    (hΦ : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞
      (fun p : ℝ × M => Φ p.1 p.2) (T ×ˢ univ))
    (hi : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)) :
    ContDiffOn ℝ ∞ (fun t => riemannianDiskArea (G t)
      ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u)) (T ∩ D.regular) := by
  intro t₀ ht₀
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hT.mem_nhds ht₀.1) (D.regular_isOpen.mem_nhds ht₀.2))
  have ht : t₀ ∈ Ioo (t₀ - r) (t₀ + r) := ⟨by linarith, by linarith⟩
  let D' := RealTimeInterval.openInterval (t₀ - r) (t₀ + r) t₀ ht
  have hsub : D'.carrier ⊆ T ∩ D.regular := by
    intro t ht
    apply hball
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    change t₀ - r < t ∧ t < t₀ + r at ht
    constructor <;> linarith [ht.1, ht.2]
  have hpull := metricFamilySmoothOn_parameterPullback hG hT hΦ D' rfl hsub
  have harea := hu.contDiffOn_area_metric_of_immersion hpull hi
  have heq : (fun t => riemannianDiskArea
      (Diffeomorph.pullbackMetric (G t) (Φ t)) u) =
      (fun t => riemannianDiskArea (G t)
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u)) :=
    funext (fun t => hu.area_pullback (G t) (Φ t))
  rw [heq] at harea
  exact (harea.contDiffAt (D'.regular_isOpen.mem_nhds ht)).contDiffWithinAt

end DifferentialGeometry.Geometry
