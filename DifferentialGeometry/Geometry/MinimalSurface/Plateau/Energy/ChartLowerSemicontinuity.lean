import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.Coordinates
import DifferentialGeometry.Analysis.Integration.Integral.WeightedLowerSemicontinuity
import DifferentialGeometry.Topology.Manifold.PartitionOfUnity
import Mathlib.Topology.Algebra.InfiniteSum.Real
import DifferentialGeometry.Analysis.Sobolev.Manifold.ChartEnergy.Density
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

section

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_chart_partition_energy_le_liminf
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (u : ℕ → C(closedDisk, M)) (v : ℂ → M) {A : ℝ}
    (hLip : ∀ n, ∃ C : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (C : ℝ≥0∞) * edist z w)
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z)))
    (henergy : ∀ n, (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u n)) z) ≤ A) :
    ∃ (ι : Type u), Countable ι ∧ ∃ (center : ι → M)
      (χ : ∀ i, SmoothBumpFunction 𝓘(ℝ, E) (center i))
      (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M univ),
      (∀ i, HasCompactSupport (ρ i : M → ℝ)) ∧
      (∀ i, tsupport (ρ i : M → ℝ) ⊆
        interior {p | χ i p = 1} ∩ (extChartAt 𝓘(ℝ, E) (center i)).source) ∧
      let Φ (i : ι) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞ :=
        (extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ (center i)).symm
      let P (i : ι) (p : M) : EuclideanSpace ℝ (Fin m) := L (χ i p • (Φ i).symm p)
      let B (i : ι) (p : M) : EuclideanSpace ℝ (Fin m) →L[ℝ]
          EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
        (ρ i p • pullbackMetricCoefficients g (Φ i) ((Φ i).symm p)).bilinearComp
          L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
      let e := Complex.orthonormalBasisOneI.repr.symm
      ∃ hv : ∀ i, ∀ k : Fin m,
          DeGiorgi.MemW1pWitness 2 (fun x => P i (v (e x)) k) (ball 0 1),
        let a (i : ι) : ℝ := (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball 0 1,
          B i (v (e x)) (WithLp.toLp 2 (fun k => (hv i k).weakGrad x j))
            (WithLp.toLp 2 (fun k => (hv i k).weakGrad x j)))
        (∀ i, 0 ≤ a i) ∧
        (∀ s : Finset ι, (∑ i ∈ s, a i) ≤ liminf (fun n => ∫ z in closedBall (0 : ℂ) 1,
          diskMapEnergyDensity g (diskExtension (u n)) z) atTop) ∧
        Summable a ∧ (∑' i, a i) ≤ liminf (fun n => ∫ z in closedBall (0 : ℂ) 1,
          diskMapEnergyDensity g (diskExtension (u n)) z) atTop := by
  classical
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let χ₀ (p : M) : SmoothBumpFunction 𝓘(ℝ, E) p := Classical.choice inferInstance
  obtain ⟨ι, hι, center, ρ, hρc, hρsupport, _, _⟩ :=
    exists_countable_compactly_supported_chart_partition χ₀
  let χ (i : ι) : SmoothBumpFunction 𝓘(ℝ, E) (center i) := χ₀ (center i)
  let Φ (i : ι) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞ :=
    (extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ (center i)).symm
  let P (i : ι) (p : M) : EuclideanSpace ℝ (Fin m) := L (χ i p • (Φ i).symm p)
  let B (i : ι) (p : M) : EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
    (ρ i p • pullbackMetricCoefficients g (Φ i) ((Φ i).symm p)).bilinearComp
      L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
  let e := Complex.orthonormalBasisOneI.repr.symm
  have hχsupport (i : ι) : tsupport (χ i : M → ℝ) ⊆ (Φ i).target := by
    change tsupport (χ i : M → ℝ) ⊆ (extChartAt 𝓘(ℝ, E) (center i)).source
    rw [extChartAt_source]
    exact (χ i).tsupport_subset_chartAt_source
  have hρtarget (i : ι) : tsupport (ρ i : M → ℝ) ⊆
      interior {p | χ i p = 1} ∩ (Φ i).target := hρsupport i
  have hlocal (i : ι) : ∃ hv : ∀ k : Fin m,
      DeGiorgi.MemW1pWitness 2 (fun x => P i (v (e x)) k) (ball 0 1),
      (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball 0 1,
        B i (v (e x)) (WithLp.toLp 2 (fun k => (hv k).weakGrad x j))
          (WithLp.toLp 2 (fun k => (hv k).weakGrad x j))) ≤
        liminf (fun n => ∫ z in closedBall (0 : ℂ) 1,
          ρ i (diskExtension (u n) z) * diskMapEnergyDensity g (diskExtension (u n)) z)
          atTop := by
    exact exists_weighted_chart_energy_le_liminf_of_cutoffs g L (Φ i) (χ i) (ρ i)
      (χ i).contMDiff (χ i).hasCompactSupport (hχsupport i)
      (ρ i).contMDiff (hρc i) (ρ.nonneg i) (hρtarget i) u v hLip hae henergy
  choose hv hlocalbound using hlocal
  let a (i : ι) : ℝ := (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball 0 1,
    B i (v (e x)) (WithLp.toLp 2 (fun k => (hv i k).weakGrad x j))
      (WithLp.toLp 2 (fun k => (hv i k).weakGrad x j)))
  have ha0 (i : ι) : 0 ≤ a i := by
    apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply Finset.sum_nonneg
    intro j _
    apply integral_nonneg
    intro x
    change 0 ≤ ρ i (v (e x)) * pullbackMetricCoefficients g (Φ i) ((Φ i).symm (v (e x)))
      (L.symm (WithLp.toLp 2 (fun k => (hv i k).weakGrad x j)))
      (L.symm (WithLp.toLp 2 (fun k => (hv i k).weakGrad x j)))
    exact mul_nonneg (ρ.nonneg i _) ((pullbackMetricCoefficients_isPosSemidef
      g (Φ i) ((Φ i).symm (v (e x)))).isNonneg.nonneg _)
  have hfinite (s : Finset ι) : (∑ i ∈ s, a i) ≤
      liminf (fun n => ∫ z in closedBall (0 : ℂ) 1,
        diskMapEnergyDensity g (diskExtension (u n)) z) atTop := by
    let : MeasurableSpace M := borel M
    let : BorelSpace M := ⟨rfl⟩
    have hU (n : ℕ) : AEMeasurable (diskExtension (u n))
        (volume.restrict (closedBall (0 : ℂ) 1)) :=
      ((u n).continuous.comp diskRetraction_lipschitz.continuous).measurable.aemeasurable
    have hInt (n : ℕ) : IntegrableOn (diskMapEnergyDensity g (diskExtension (u n)))
        (closedBall (0 : ℂ) 1) := by
      obtain ⟨C, hC⟩ := hLip n
      exact integrable_diskMapEnergyDensity g hC
    have hnonneg (n : ℕ) : ∀ᵐ z ∂volume.restrict (closedBall (0 : ℂ) 1),
        0 ≤ diskMapEnergyDensity g (diskExtension (u n)) z :=
      Eventually.of_forall fun z => div_nonneg
        (add_nonneg (metric_inner_self_nonneg g _ _) (metric_inner_self_nonneg g _ _))
        (by norm_num)
    exact ρ.toPartitionOfUnity.sum_le_liminf_integral_of_weighted_liminf s
      (fun n => diskExtension (u n)) hU
      (fun n => diskMapEnergyDensity g (diskExtension (u n))) hInt hnonneg henergy a
      (fun i _ => hlocalbound i)
  exact ⟨ι, hι, center, χ, ρ, hρc, hρsupport, hv, ha0, hfinite,
    summable_of_sum_le ha0 hfinite, Real.tsum_le_of_sum_le ha0 hfinite⟩

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Metric
open DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] {M : Type u} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_chart_partition_energy_density_le_liminf
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (u : ℕ → C(closedDisk, M)) (v : ℂ → M) {A : ℝ}
    (hLip : ∀ n, ∃ C : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (C : ℝ≥0∞) * edist z w)
    (hae : ∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
      Tendsto (fun n => diskExtension (u n) z) atTop (𝓝 (v z)))
    (henergy : ∀ n, (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u n)) z) ≤ A) :
    ∃ (ι : Type u), Countable ι ∧ ∃ (center : ι → M)
      (χ : ∀ i, SmoothBumpFunction 𝓘(ℝ, E) (center i))
      (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) M univ),
      (∀ i, HasCompactSupport (ρ i : M → ℝ)) ∧
      (∀ i, tsupport (ρ i : M → ℝ) ⊆
        interior {p | χ i p = 1} ∩ (extChartAt 𝓘(ℝ, E) (center i)).source) ∧
      let Φ (i : ι) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞ :=
        (extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ (center i)).symm
      let P (i : ι) (p : M) : EuclideanSpace ℝ (Fin m) := L (χ i p • (Φ i).symm p)
      let e := Complex.orthonormalBasisOneI.repr.symm
      ∃ hw : ∀ i, ∀ k : Fin m,
          DeGiorgi.MemW1pWitness 2 (fun x => P i (v (e x)) k) (ball 0 1),
        let D := chartPartitionEnergyDensity g L Φ (fun i => χ i)
          ρ.toPartitionOfUnity (fun x => v (e x)) hw
        (∀ x, 0 ≤ D x) ∧ Integrable D (volume.restrict (ball 0 1)) ∧
          (∫ x in ball 0 1, D x) ≤ liminf (fun n => ∫ z in closedBall (0 : ℂ) 1,
            diskMapEnergyDensity g (diskExtension (u n)) z) atTop := by
  classical
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  let : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace 𝓘(ℝ, E) M
  obtain ⟨ι, hι, center, χ, ρ, hρc, hρsupport, hw, _, _, hsummable, hbound⟩ :=
    exists_chart_partition_energy_le_liminf g L u v hLip hae henergy
  let : Countable ι := hι
  let Φ (i : ι) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E M ∞ :=
    (extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ (center i)).symm
  let B (i : ι) (p : M) : EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ :=
    (ρ i p • pullbackMetricCoefficients g (Φ i) ((Φ i).symm p)).bilinearComp
      L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := Complex.orthonormalBasisOneI.repr.symm
  let w : EuclideanSpace ℝ (Fin 2) → M := fun x => v (e x)
  let a (i : ι) : ℝ := (1 / 2 : ℝ) * (∑ j : Fin 2, ∫ x in ball 0 1,
    B i (w x) (WithLp.toLp 2 (fun k => (hw i k).weakGrad x j))
      (WithLp.toLp 2 (fun k => (hw i k).weakGrad x j)))
  change Summable a at hsummable
  change (∑' i, a i) ≤ _ at hbound
  have hball : e ⁻¹' ball (0 : ℂ) 1 = ball (0 : EuclideanSpace ℝ (Fin 2)) 1 := by
    ext x
    simp only [mem_preimage, mem_ball_zero_iff, e.norm_map]
  have he := e.measurePreserving.restrict_preimage (s := ball (0 : ℂ) 1) measurableSet_ball
  rw [hball] at he
  have hwm : AEMeasurable w (volume.restrict (ball 0 1)) :=
    aemeasurable_of_tendsto_metrizable_ae' (fun n =>
      (((u n).continuous.comp diskRetraction_lipschitz.continuous).comp
        e.continuous).measurable.aemeasurable)
      (he.quasiMeasurePreserving.ae hae)
  have hρtarget (i : ι) : tsupport (ρ i : M → ℝ) ⊆ (Φ i).target :=
    fun p hp => (hρsupport i hp).2
  have hterm (i : ι) : (∫ x in ball 0 1,
      ρ i (w x) * weakChartEnergyDensity g L (Φ i) (χ i) w (hw i) x) = a i := by
    have hi := (weighted_chart_energy_density_nonneg_integrable g (Φ i) L (χ i) (ρ i)
      (ρ i).contMDiff.continuous (hρc i) (hρtarget i) (ρ.nonneg i) hwm (hw i)).2.2.2
    calc
      (∫ x in ball 0 1, ρ i (w x) * weakChartEnergyDensity g L (Φ i) (χ i) w (hw i) x) =
          ∫ x in ball 0 1, (1 / 2 : ℝ) * ∑ j : Fin 2,
            B i (w x) (WithLp.toLp 2 (fun k => (hw i k).weakGrad x j))
              (WithLp.toLp 2 (fun k => (hw i k).weakGrad x j)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [weakChartEnergyDensity, B, ContinuousLinearMap.bilinearComp_apply,
          ContinuousLinearEquiv.coe_coe, smul_apply, smul_eq_mul]
        rw [← Finset.mul_sum]
        ring
      _ = a i := hi
  have hs : Summable (fun i => ∫ x in ball 0 1,
      ρ i (w x) * weakChartEnergyDensity g L (Φ i) (χ i) w (hw i) x) := by
    simpa only [hterm] using hsummable
  obtain ⟨hint, hintEq⟩ := integrable_chartPartitionEnergyDensity g L Φ (fun i => χ i)
    ρ.toPartitionOfUnity hρc hρtarget hwm hw hs
  have hnonneg (x : EuclideanSpace ℝ (Fin 2)) :
      0 ≤ chartPartitionEnergyDensity g L Φ (fun i => χ i) ρ.toPartitionOfUnity w hw x :=
    tsum_nonneg fun i => mul_nonneg (ρ.nonneg i _)
      (weakChartEnergyDensity_nonneg g L (Φ i) (χ i) w (hw i) x)
  refine ⟨ι, hι, center, χ, ρ, hρc, hρsupport, hw, hnonneg, hint, ?_⟩
  rw [hintEq]
  change (∑' i, ∫ x in ball 0 1,
    ρ i (w x) * weakChartEnergyDensity g L (Φ i) (χ i) w (hw i) x) ≤ _
  simpa only [hterm] using hbound

end DifferentialGeometry.Geometry

end

end
