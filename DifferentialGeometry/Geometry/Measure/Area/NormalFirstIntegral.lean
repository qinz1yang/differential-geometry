import DifferentialGeometry.Geometry.Measure.Area.NormalFirstVariation
import DifferentialGeometry.Geometry.Measure.Area.InducedVolume
import DifferentialGeometry.Geometry.MinimalSurface.Curvature.DiskNormalTraceContinuity
import DifferentialGeometry.Geometry.MinimalSurface.Variation.ImmersedDiskFirstVariation
import DifferentialGeometry.Geometry.Metric.Family.Stationary
import DifferentialGeometry.Geometry.Metric.TensorInner.Fiber.MetricData
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Integrated normal first variation on the original disk

The original immersion, induced metric, induced volume and normal section are
fixed before any compact scalar test or realizing ambient field is chosen.
The derivative is assembled from the existing immersed-disk integral engine,
normal density derivative and induced-volume identity with one area density.
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry
open DifferentialGeometry.Geometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff _root_.Topology BigOperators

namespace DifferentialGeometry.Geometry

local notation "D" => TopologicalSpace.Opens.mk (Metric.ball (0 : ℂ) 1) Metric.isOpen_ball

private local instance : MeasurableSpace D := borel D
private local instance : BorelSpace D := ⟨rfl⟩
private local instance : LocallyCompactSpace D :=
  (D : TopologicalSpace.Opens ℂ).isOpen.locallyCompactSpace
private local instance : SigmaCompactSpace D := by infer_instance

private theorem exists_disk_orthonormal_basis
    (gD : SmoothRiemannianMetric 𝓘(ℝ, ℂ) D) (q : D) :
    ∃ b : Module.Basis (Fin 2) ℝ (TangentSpace 𝓘(ℝ, ℂ) q),
      ∀ i j, gD.inner q (b i) (b j) = if i = j then 1 else 0 := by
  classical
  have hBasis (V : Type) [AddCommGroup V] [Module ℝ V]
      [FiniteDimensional ℝ V] (data : MetricFiberData V)
      (hdim : Module.finrank ℝ V = 2) :
      ∃ b : Module.Basis (Fin 2) ℝ V,
        ∀ i j, data.inner (b i) (b j) = if i = j then 1 else 0 := by
    let addV : AddCommGroup V := inferInstance
    let modV : Module ℝ V := inferInstance
    let : InnerProductSpace.Core ℝ V := data.toCore
    let : NormedAddCommGroup V :=
      @InnerProductSpace.Core.toNormedAddCommGroup ℝ V _ addV modV data.toCore
    let : AddCommGroup V := addV
    let : Module ℝ V := modV
    let : InnerProductSpace ℝ V :=
      @InnerProductSpace.ofCore ℝ V _ _ _ data.toCore.toCore
    let ob : OrthonormalBasis (Fin 2) ℝ V :=
      (stdOrthonormalBasis ℝ V).reindex (finCongr hdim)
    refine ⟨ob.toBasis, ?_⟩
    intro i j
    rw [← MetricFiberData.toCore_inner data]
    exact ob.inner_eq_ite i j
  let metricData := tangentMetricData (I := 𝓘(ℝ, ℂ)) gD q
  have hdim : Module.finrank ℝ ℂ = 2 := by
    rw [Module.finrank_eq_card_basis Complex.basisOneI, Fintype.card_fin]
  obtain ⟨b, hb⟩ := @hBasis ℂ
    (inferInstance : AddCommGroup ℂ) (inferInstance : Module ℝ ℂ)
    (inferInstance : FiniteDimensional ℝ ℂ) metricData.metric hdim
  refine ⟨b, ?_⟩
  intro i j
  exact (TangentMetricData.inner_eq metricData (b i) (b j)).symm.trans (hb i j)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]

/-- Integrated first variation for the same original disk under a supplied
canonical compact ambient flow with the stated normal speed. This does not
assert the existence of a realizing field for every compact test. -/
theorem SmoothDiskExtension.hasDerivAt_diskArea_normal_compactSupportFlow
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (u : C(closedDisk, M)) (U : ℂ → M)
    (hExt : SmoothDiskExtension (E := E) u U)
    (hImm : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    (hUD : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun q : D => U q))
    (hiD : ∀ q : D, Function.Injective
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : D => U p) q))
    (ν : ∀ q : D, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : Continuous
      (fun q : D => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (hnormal : ∀ (q : D) (v : ℂ),
      g.inner (U q) (ν q)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : D => U p) q v) = 0) :
    let f : D → M := fun q => U q
    let gD := g.pullback f hUD hiD
    let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) gD
    let H : D → ℝ := fun q =>
      let II := secondFundamentalFormAmbientAt gD g f q
      let A := g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q 1)
      let B := g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q Complex.I)
      let C := g.inner (U q) (diskMapPartial U q Complex.I) (diskMapPartial U q Complex.I)
      (C * g.inner (U q) (ν q) (II (1 : ℂ) (1 : ℂ)) +
          A * g.inner (U q) (ν q) (II Complex.I Complex.I) -
          2 * B * g.inner (U q) (ν q) (II (1 : ℂ) Complex.I)) /
        (A * C - B ^ 2)
    ∀ (φ : D → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
      Integrable (fun q => φ q * H q) μ ∧
      ∀ (X : ∀ x : M, TangentSpace 𝓘(ℝ, E) x)
        (hX : ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
          (fun x : M => (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)))
        (hXc : HasCompactSupport X),
        (∀ q : D,
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
            (fun t => Diffeomorph.compactSupportFlow X hX hXc t (U q)) 0 (1 : ℝ) : E) =
              φ q • ν q) →
        HasDerivAt (fun t => riemannianDiskArea g
          ((⟨Diffeomorph.compactSupportFlow X hX hXc t,
            (Diffeomorph.compactSupportFlow X hX hXc t).contMDiff.continuous⟩ : C(M, M)).comp u))
          (-(∫ q : D, φ q * H q ∂μ)) 0 := by
  classical
  let f : D → M := fun q => U q
  let gD := g.pullback f hUD hiD
  let μ := riemannianVolumeMeasure (I := 𝓘(ℝ, ℂ)) (M := D) gD
  let H : D → ℝ := fun q =>
    let II := secondFundamentalFormAmbientAt gD g f q
    let A := g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q 1)
    let B := g.inner (U q) (diskMapPartial U q 1) (diskMapPartial U q Complex.I)
    let C := g.inner (U q) (diskMapPartial U q Complex.I) (diskMapPartial U q Complex.I)
    (C * g.inner (U q) (ν q) (II (1 : ℂ) (1 : ℂ)) +
        A * g.inner (U q) (ν q) (II Complex.I Complex.I) -
        2 * B * g.inner (U q) (ν q) (II (1 : ℂ) Complex.I)) /
      (A * C - B ^ 2)
  change ∀ (φ : D → ℝ), ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ → HasCompactSupport φ →
    Integrable (fun q => φ q * H q) μ ∧ _
  have hH : Continuous H :=
    continuous_normal_scalar_secondFundamentalForm_disk_trace
      D g U hUD hiD ν hν hnormal
  let : IsLocallyFiniteMeasure μ := riemannianVolumeMeasure_isLocallyFiniteMeasure gD
  intro φ hφ hφc
  refine ⟨?_, ?_⟩
  · simpa only [smul_eq_mul] using
      hH.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  intro X hX hXc hvelocity
  let Φ := Diffeomorph.compactSupportFlow X hX hXc
  let G : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) M :=
    fun t => Diffeomorph.pullbackMetric g (Φ t)
  let Q : ℂ → ℝ := diskMapGramMetricVariationDensity G 0 U
  let T := RealTimeInterval.univ 0
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hconstant : MetricFamilySmoothOn T (fun _ : ℝ => g) :=
    metricFamilySmoothOn_stationary g T
  have hfamily : MetricFamilySmoothOn T G :=
    metricFamilySmoothOn_parameterPullback hconstant isOpen_univ
      (Diffeomorph.contMDiff_compactSupportFlow X hX hXc).contMDiffOn
      T rfl (fun _ _ => ⟨mem_univ _, mem_univ _⟩)
  have hbase := hExt.hasDerivAt_riemannianDiskArea_isotopy_of_immersion
    hconstant (show T.regular ∈ 𝓝 (0 : ℝ) from Filter.univ_mem)
    (Φ := Φ) isOpen_univ (mem_univ (0 : ℝ))
    (Diffeomorph.contMDiff_compactSupportFlow X hX hXc).contMDiffOn hImm
  have hnormalU : ∀ (q : D) (v : ℂ),
      g.inner (U q) (ν q) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q v) = 0 := by
    intro q v
    have hdf : (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun p : D => U p) q : ℂ →L[ℝ] E) =
        mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q :=
      DifferentialGeometry.mfderiv_restrict_open U D q
    exact (congrArg (fun L : ℂ →L[ℝ] E => g.inner (U q) (ν q) (L v)) hdf).symm.trans
      (hnormal q v)
  let J : D → ℝ := fun q => riemannianAreaDensity g U q
  have hpoint (q : D) : Q q = -φ q * J q * H q := by
    obtain ⟨b, hb⟩ := exists_disk_orthonormal_basis gD q
    have hdensity := hasDerivAt_compactSupportFlow_areaDensity_of_normal_velocity
      D g U hUD hiD ν hnormalU φ X hX hXc hvelocity q b hb
    have hUz : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U q :=
      DifferentialGeometry.mdifferentiableAt_subtype_iff.mp
        (hUD.mdifferentiableAt (x := q) (by simp))
    have hpullback := hdensity.congr_of_eventuallyEq
      (Eventually.of_forall (fun t => riemannianAreaDensity_pullback g (Φ t) hUz))
    have hGram := hasDerivAt_diskMapAreaDensity_metric_of_immersion hfamily
      (show T.regular ∈ 𝓝 (0 : ℝ) from Filter.univ_mem)
      (hImm q (Metric.ball_subset_closedBall q.property))
    have htrace : H q = ∑ i : Fin 2, g.inner (U q) (ν q)
        (secondFundamentalFormAmbientAt gD g f q (b i) (b i)) :=
      (normal_scalar_secondFundamentalForm_disk_trace_eq_sum_orthonormal
        D g U hUD hiD q (ν q) b hb).2
    exact (hGram.unique hpullback).trans
      (congrArg (fun r : ℝ => -φ q * J q * r) htrace.symm)
  let μD := MeasureTheory.Measure.comap (Subtype.val : D → ℂ) (volume : MeasureTheory.Measure ℂ)
  have hUon : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U (D : Set ℂ) := by
    intro z hz
    exact (contMDiffAt_subtype_iff.mp
      (hUD.contMDiffAt (x := (⟨z, hz⟩ : D)))).contMDiffWithinAt
  have hJc : Continuous J :=
    (continuousOn_riemannianAreaDensity g (D : TopologicalSpace.Opens ℂ).isOpen
      (hUon.of_le (by simp))).domRestrict
  have hJm : Measurable (fun q => ENNReal.ofReal (J q)) :=
    ENNReal.measurable_ofReal.comp hJc.measurable
  have hJfinite : ∀ᵐ q ∂μD, ENNReal.ofReal (J q) < (⊤ : ENNReal) :=
    Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hvol := riemannianVolumeMeasure_induced_complex_open D g U hUD hiD
  change μ = μD.withDensity (fun q => ENNReal.ofReal (J q)) at hvol
  have hvolIntegral : (∫ q : D, φ q * H q ∂μ) =
      ∫ q : D, J q * (φ q * H q) ∂μD := by
    rw [hvol, integral_withDensity_eq_integral_toReal_smul hJm hJfinite]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => by
      change (ENNReal.ofReal (J q)).toReal * (φ q * H q) = J q * (φ q * H q)
      rw [ENNReal.toReal_ofReal (riemannianAreaDensity_nonneg g U q)]
  have hval : MeasurableEmbedding (Subtype.val : D → ℂ) :=
    (D : TopologicalSpace.Opens ℂ).isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
      (mα := borel D)
  have hsubtype : (∫ q : D, Q q ∂μD) = ∫ z in Metric.ball (0 : ℂ) 1, Q z := by
    have hmap := hval.integral_map (μ := μD) Q
    rw [hval.map_comap, Subtype.range_coe] at hmap
    exact hmap.symm
  have hnosphere : ∀ᵐ z : ℂ ∂volume, z ∉ Metric.sphere (0 : ℂ) 1 :=
    measure_eq_zero_iff_ae_notMem.mp (MeasureTheory.Measure.addHaar_sphere volume (0 : ℂ) 1)
  have hsets : Metric.closedBall (0 : ℂ) 1 =ᵐ[volume] Metric.ball (0 : ℂ) 1 := by
    filter_upwards [hnosphere] with z hz
    apply propext
    constructor
    · intro hzclosed
      exact lt_of_le_of_ne hzclosed hz
    · intro hzball
      exact Metric.mem_closedBall.mpr (le_of_lt (Metric.mem_ball.mp hzball))
  have hintegral : (∫ z in Metric.closedBall (0 : ℂ) 1, Q z) =
      -(∫ q : D, φ q * H q ∂μ) := by
    calc
      (∫ z in Metric.closedBall (0 : ℂ) 1, Q z) =
          ∫ z in Metric.ball (0 : ℂ) 1, Q z := setIntegral_congr_set hsets
      _ = ∫ q : D, Q q ∂μD := hsubtype.symm
      _ = ∫ q : D, -(J q * (φ q * H q)) ∂μD := by
        apply integral_congr_ae
        exact Eventually.of_forall fun q => by
          change Q q = -(J q * (φ q * H q))
          rw [hpoint q]
          ring
      _ = -(∫ q : D, J q * (φ q * H q) ∂μD) := integral_neg _
      _ = -(∫ q : D, φ q * H q ∂μ) := congrArg Neg.neg hvolIntegral.symm
  have hd := hbase.2
  change HasDerivAt (fun t => riemannianDiskArea g
    ((⟨Φ t, (Φ t).contMDiff.continuous⟩ : C(M, M)).comp u))
    (∫ z in Metric.closedBall (0 : ℂ) 1, Q z) 0 at hd
  rw [hintegral] at hd
  exact hd

end DifferentialGeometry.Geometry
