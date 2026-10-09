import DifferentialGeometry.Geometry.Measure.Area.ImmersedMetricSmoothness
import DifferentialGeometry.Geometry.Metric.Family.Stationary
import DifferentialGeometry.Topology.Diffeomorph.Flow

/- Scratch only. Both differentiations use the existing compact-source
integral theorem, whose tube-lemma proof produces the uniform local majorant.
No bound on a derivative, or identity for the area derivative, is assumed. -/

set_option autoImplicit false
noncomputable section

open Set Filter Bundle Manifold MeasureTheory
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Topology ContDiff Bundle Manifold

namespace DifferentialGeometry.Geometry

private theorem hasDerivAt_integral_compactOn_scalar
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasure μ] {T : Set ℝ} (hT : IsOpen T)
    (f d : ℝ → X → ℝ)
    (hf : ContinuousOn (fun p : ℝ × X => f p.1 p.2) (T ×ˢ univ))
    (hd : ContinuousOn (fun p : ℝ × X => d p.1 p.2) (T ×ˢ univ))
    (hderiv : ∀ t ∈ T, ∀ x, HasDerivAt (fun s => f s x) (d t x) t)
    {t : ℝ} (ht : t ∈ T) :
    HasDerivAt (fun s => ∫ x, f s x ∂μ) (∫ x, d t x ∂μ) t := by
  let L : ℝ → X → ℝ →L[ℝ] ℝ := fun s x =>
    ContinuousLinearMap.toSpanSingleton ℝ (d s x)
  have hL : ContinuousOn (fun p : ℝ × X => L p.1 p.2) (T ×ˢ univ) :=
    (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.comp_continuousOn hd
  have hI : Integrable (L t) μ := by
    have hc : Continuous (L t) := by
      rw [← continuousOn_univ]
      exact hL.comp (continuousOn_const.prodMk continuousOn_id)
        (fun x _ => ⟨ht, mem_univ x⟩)
    exact integrableOn_univ.mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  have hh := (hasFDerivAt_integral_compactOn μ hT f L hf hL
    (fun s hs x => (hderiv s hs x).hasFDerivAt) t ht).hasDerivAt
  rw [ContinuousLinearMap.integral_apply hI] at hh
  simpa only [L, ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hh

/-- The scalar density and both of its time derivatives are the actual ones.
The open joint domain contains one entire time-set times the compact source. -/
private theorem hasDerivAt_deriv_setIntegral_of_smooth
    {K : Set ℂ} (hK : IsCompact K) {T : Set ℝ} {Ω : Set (ℝ × ℂ)}
    (hT : IsOpen T) (hΩ : IsOpen Ω) (hsub : T ×ˢ K ⊆ Ω)
    {f : ℝ × ℂ → ℝ} (hf : ContDiffOn ℝ ∞ f Ω)
    {t₀ : ℝ} (ht₀ : t₀ ∈ T) :
    IntegrableOn (fun z => deriv (deriv (fun t => f (t, z))) t₀) K ∧
      HasDerivAt (deriv (fun t => ∫ z in K, f (t, z)))
        (∫ z in K, deriv (deriv (fun t => f (t, z))) t₀) t₀ := by
  let D1 : ℝ × ℂ → ℝ := fun p => fderiv ℝ f p (1, 0)
  let D2 : ℝ × ℂ → ℝ := fun p => fderiv ℝ D1 p (1, 0)
  have hD1 : ContDiffOn ℝ ∞ D1 Ω :=
    (hf.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hD2 : ContDiffOn ℝ ∞ D2 Ω :=
    (hD1.fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const
  have hd (t : ℝ) (ht : t ∈ T) (z : ℂ) (hz : z ∈ K) :
      HasDerivAt (fun s => f (s, z)) (D1 (t, z)) t := by
    have hp : (t, z) ∈ Ω := hsub ⟨ht, hz⟩
    exact ((hf.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
  have hd1 (t : ℝ) (ht : t ∈ T) (z : ℂ) (hz : z ∈ K) :
      HasDerivAt (fun s => D1 (s, z)) (D2 (t, z)) t := by
    have hp : (t, z) ∈ Ω := hsub ⟨ht, hz⟩
    exact ((hD1.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt
      |>.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
  have hD2eq (z : ℂ) (hz : z ∈ K) :
      deriv (deriv (fun t => f (t, z))) t₀ = D2 (t₀, z) := by
    have heq : deriv (fun t => f (t, z)) =ᶠ[𝓝 t₀] fun t => D1 (t, z) := by
      filter_upwards [hT.mem_nhds ht₀] with t ht
      exact (hd t ht z hz).deriv
    exact ((hd1 t₀ ht₀ z hz).congr_of_eventuallyEq heq).deriv
  have hint : IntegrableOn (fun z => deriv (deriv (fun t => f (t, z))) t₀) K := by
    have hc : ContinuousOn (fun z => D2 (t₀, z)) K :=
      hD2.continuousOn.comp (continuousOn_const.prodMk continuousOn_id)
        (fun z hz => hsub ⟨ht₀, hz⟩)
    exact (hc.congr hD2eq).integrableOn_compact hK
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : MeasureSpace K := MeasureTheory.Measure.Subtype.measureSpace
  let : IsFiniteMeasure (volume : Measure K) := {
    measure_univ_lt_top := by
      rw [MeasureTheory.Measure.Subtype.volume_univ hK.measurableSet.nullMeasurableSet]
      exact hK.measure_lt_top }
  have hc : ContinuousOn (fun p : ℝ × K => f (p.1, p.2)) (T ×ˢ univ) :=
    hf.continuousOn.comp (by fun_prop) (fun p hp => hsub ⟨hp.1, p.2.property⟩)
  have hc1 : ContinuousOn (fun p : ℝ × K => D1 (p.1, p.2)) (T ×ˢ univ) :=
    hD1.continuousOn.comp (by fun_prop) (fun p hp => hsub ⟨hp.1, p.2.property⟩)
  have hc2 : ContinuousOn (fun p : ℝ × K => D2 (p.1, p.2)) (T ×ˢ univ) :=
    hD2.continuousOn.comp (by fun_prop) (fun p hp => hsub ⟨hp.1, p.2.property⟩)
  have hfirst (t : ℝ) (ht : t ∈ T) :
      HasDerivAt (fun s => ∫ z : K, f (s, z)) (∫ z : K, D1 (t, z)) t :=
    hasDerivAt_integral_compactOn_scalar volume hT
      (fun s (z : K) => f (s, z)) (fun s (z : K) => D1 (s, z)) hc hc1
      (fun s hs z => hd s hs z z.property) ht
  have hsecond : HasDerivAt (fun t => ∫ z : K, D1 (t, z))
      (∫ z : K, D2 (t₀, z)) t₀ :=
    hasDerivAt_integral_compactOn_scalar volume hT
      (fun s (z : K) => D1 (s, z)) (fun s (z : K) => D2 (s, z)) hc1 hc2
      (fun s hs z => hd1 s hs z z.property) ht₀
  have heq : deriv (fun t => ∫ z : K, f (t, z)) =ᶠ[𝓝 t₀]
      fun t => ∫ z : K, D1 (t, z) := by
    filter_upwards [hT.mem_nhds ht₀] with t ht
    exact (hfirst t ht).deriv
  have hsecond' := hsecond.congr_of_eventuallyEq heq
  have harea : (fun t => ∫ z : K, f (t, z)) = (fun t => ∫ z in K, f (t, z)) :=
    funext (fun t => integral_subtype hK.measurableSet (fun z => f (t, z)))
  have hcoeff : (∫ z : K, D2 (t₀, z)) =
      ∫ z in K, deriv (deriv (fun t => f (t, z))) t₀ := by
    calc
      (∫ z : K, D2 (t₀, z)) = ∫ z in K, D2 (t₀, z) :=
        integral_subtype hK.measurableSet (fun z : ℂ => D2 (t₀, z))
      _ = _ := setIntegral_congr_fun hK.measurableSet (fun z hz => (hD2eq z hz).symm)
  rw [harea, hcoeff] at hsecond'
  exact ⟨hint, hsecond'⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Second differentiation under the integral for the actual area of one smooth
immersed disk in a smooth metric family. Immersion is required through the
closed disk, which makes the actual Gram determinant strictly positive there. -/
theorem hasDerivAt_deriv_diskArea_metric_integral
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    {D : RealTimeInterval} {G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hG : MetricFamilySmoothOn D G)
    (hi : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    {t₀ : ℝ} (ht₀ : t₀ ∈ D.regular) :
    IntegrableOn
        (fun z => deriv (deriv (fun t => riemannianAreaDensity (G t) U z)) t₀)
        (Metric.closedBall (0 : ℂ) 1) ∧
      HasDerivAt (deriv (fun t => riemannianDiskArea (G t) u))
        (∫ z in Metric.closedBall (0 : ℂ) 1,
          deriv (deriv (fun t => riemannianAreaDensity (G t) U z)) t₀) t₀ := by
  obtain ⟨heq, s, hs, hDs, hU⟩ := hu
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
  have hsub : D.regular ×ˢ Metric.closedBall (0 : ℂ) 1 ⊆ Ω := by
    intro p hp
    refine ⟨⟨hp.1, hDs hp.2⟩, ?_⟩
    exact Real.sqrt_pos.mp (riemannianAreaDensity_pos_of_injective_mfderiv
      (G p.1) (hi p.2 hp.2))
  have hdensity : ContDiffOn ℝ ∞
      (fun p : ℝ × ℂ => riemannianAreaDensity (G p.1) U p.2) Ω :=
    (hQ.mono inter_subset_left).sqrt (fun p hp => ne_of_gt hp.2)
  have hh := hasDerivAt_deriv_setIntegral_of_smooth
    (isCompact_closedBall (0 : ℂ) 1) D.regular_isOpen hΩ hsub hdensity ht₀
  have harea : (fun t => riemannianDiskArea (G t) u) =
      (fun t => ∫ z in Metric.closedBall (0 : ℂ) 1, riemannianAreaDensity (G t) U z) :=
    funext (fun t => riemannianDiskArea_eq_of_extension (G t) u U heq)
  rw [harea]
  exact hh

/-- The canonical compactly supported flow gives the actual moving disk, in the
original fixed ambient metric. Neither an area second derivative nor its
integrable domination is a premise. The contact time is arbitrary. -/
theorem hasDerivAt_deriv_diskArea_compactSupportFlow_integral [T2Space M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {u : C(closedDisk, M)} {U : ℂ → M} (hu : SmoothDiskExtension (E := E) u U)
    (hi : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    (X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
    (hX : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x : M => (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hXc : HasCompactSupport X) (t₀ : ℝ) :
    let Φ := Diffeomorph.compactSupportFlow X hX hXc
    IntegrableOn
        (fun z => deriv (deriv (fun t => riemannianAreaDensity g (Φ t ∘ U) z)) t₀)
        (Metric.closedBall (0 : ℂ) 1) ∧
      HasDerivAt (deriv (fun t => riemannianDiskArea g
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u)))
        (∫ z in Metric.closedBall (0 : ℂ) 1,
          deriv (deriv (fun t => riemannianAreaDensity g (Φ t ∘ U) z)) t₀) t₀ := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  let D := RealTimeInterval.univ 0
  have hg : MetricFamilySmoothOn D (fun _ : ℝ => g) :=
    metricFamilySmoothOn_stationary g D
  have hG : MetricFamilySmoothOn D (fun t => Diffeomorph.pullbackMetric g (Φ t)) :=
    metricFamilySmoothOn_parameterPullback hg isOpen_univ
      (Diffeomorph.contMDiff_compactSupportFlow X hX hXc).contMDiffOn
      D rfl (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  have hh := hasDerivAt_deriv_diskArea_metric_integral hu hG hi (t₀ := t₀) (mem_univ t₀)
  have harea : (fun t => riemannianDiskArea (Diffeomorph.pullbackMetric g (Φ t)) u) =
      (fun t => riemannianDiskArea g
        ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u)) :=
    funext (fun t => hu.area_pullback g (Φ t))
  have hden (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
      (fun t => riemannianAreaDensity (Diffeomorph.pullbackMetric g (Φ t)) U z) =
        (fun t => riemannianAreaDensity g (Φ t ∘ U) z) := by
    obtain ⟨_, s, hs, hDs, hU⟩ := hu
    exact funext (fun t => riemannianAreaDensity_pullback g (Φ t)
      (((hU z (hDs hz)).contMDiffAt (hs.mem_nhds (hDs hz))).mdifferentiableAt (by simp)))
  have hcoeff :
      (∫ z in Metric.closedBall (0 : ℂ) 1,
        deriv (deriv (fun t => riemannianAreaDensity (Diffeomorph.pullbackMetric g (Φ t)) U z)) t₀) =
      ∫ z in Metric.closedBall (0 : ℂ) 1,
        deriv (deriv (fun t => riemannianAreaDensity g (Φ t ∘ U) z)) t₀ := by
    apply setIntegral_congr_fun measurableSet_closedBall
    intro z hz
    exact congrArg (fun d : ℝ → ℝ => deriv (deriv d) t₀) (hden z hz)
  refine ⟨hh.1.congr ?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_closedBall] with z hz
    rw [hden z hz]
  · rw [harea, hcoeff] at hh
    exact hh.2

end DifferentialGeometry.Geometry
