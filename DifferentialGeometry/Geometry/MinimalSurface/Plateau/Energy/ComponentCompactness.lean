import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.MetricTargetCompactness
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Energy.ChartLowerSemicontinuity
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetDifferential

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
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_component_ae_limit_chart_energy_density_le
    {m : ℕ} (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (hg : RiemannianMetricComplete g)
    (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (γ : freeLoop M) (u : ℕ → C(closedDisk, M)) (τ : ℕ → C(loopCircle, loopCircle))
    (htrace : ∀ n, diskTrace (u n) = γ.comp (τ n)) {b : ℝ}
    (hLip : ∀ n, ∃ C : ℝ≥0, ∀ z w,
      riemannianEDistOf g (u n z) (u n w) ≤ (C : ℝ≥0∞) * edist z w)
    (henergyLim : Tendsto (fun n => ∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u n)) z) atTop (𝓝 b)) :
    let C := connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)
    let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
    let uC : ℕ → C(closedDisk, C) := fun n => diskInLoopComponent γ (τ n) (u n) (htrace n)
    let : MeasurableSpace C := borel C
    ∃ (φ : ℕ → ℕ) (v : ℂ → C), StrictMono φ ∧
      AEMeasurable v (volume.restrict (ball (0 : ℂ) 1)) ∧
      (∀ n z, ((diskExtension (uC n) z : C) : M) = diskExtension (u n) z) ∧
      (∀ n z, diskMapEnergyDensity gC (diskExtension (uC n)) z =
        diskMapEnergyDensity g (diskExtension (u n)) z) ∧
      (∀ n, diskTrace (uC (φ n)) = (loopInComponent γ).comp (τ (φ n))) ∧
      (∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
        Tendsto (fun n => diskExtension (uC (φ n)) z) atTop (𝓝 (v z))) ∧
      (∀ᵐ z ∂volume.restrict (ball (0 : ℂ) 1),
        Tendsto (fun n => diskExtension (u (φ n)) z) atTop (𝓝 (v z : M))) ∧
      ∃ (ι : Type u), Countable ι ∧ ∃ (center : ι → C)
        (χ : ∀ i, SmoothBumpFunction 𝓘(ℝ, E) (center i))
        (ρ : SmoothPartitionOfUnity ι 𝓘(ℝ, E) C univ),
        (∀ i, HasCompactSupport (ρ i : C → ℝ)) ∧
        (∀ i, tsupport (ρ i : C → ℝ) ⊆
          interior {p | χ i p = 1} ∩ (extChartAt 𝓘(ℝ, E) (center i)).source) ∧
        let Φ (i : ι) : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E C ∞ :=
          (extChartAtPartialDiffeomorph 𝓘(ℝ, E) ∞ (center i)).symm
        let P (i : ι) (p : C) : EuclideanSpace ℝ (Fin m) := L (χ i p • (Φ i).symm p)
        let e := Complex.orthonormalBasisOneI.repr.symm
        ∃ hw : ∀ i, ∀ k : Fin m,
            DeGiorgi.MemW1pWitness 2 (fun x => P i (v (e x)) k) (ball 0 1),
          let D := chartPartitionEnergyDensity gC L Φ (fun i => χ i)
            ρ.toPartitionOfUnity (fun x => v (e x)) hw
          (∀ x, 0 ≤ D x) ∧ Integrable D (volume.restrict (ball 0 1)) ∧
            (∫ x in ball 0 1, D x) ≤ b := by
  classical
  obtain ⟨A, hA⟩ := henergyLim.isBoundedUnder_le.bddAbove_range
  have henergy (n : ℕ) : (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity g (diskExtension (u n)) z) ≤ A := hA (mem_range_self n)
  let C := connectedComponentOpen (I := 𝓘(ℝ, E)) (γ 0)
  let gC : SmoothRiemannianMetric 𝓘(ℝ, E) C := g.restrictOpen C
  let uC : ℕ → C(closedDisk, C) := fun n => diskInLoopComponent γ (τ n) (u n) (htrace n)
  let : MeasurableSpace C := borel C
  let : SigmaCompactSpace C := sigmaCompactSpace_connectedComponent_of_riemannianMetric g (γ 0)
  have hgC : RiemannianMetricComplete gC := hg.restrict_connectedComponent g (γ 0)
  have hUC (n : ℕ) (z : ℂ) : ((diskExtension (uC n) z : C) : M) = diskExtension (u n) z := rfl
  have hLipC (n : ℕ) : ∃ K : ℝ≥0, ∀ z w,
      riemannianEDistOf gC (uC n z) (uC n w) ≤ (K : ℝ≥0∞) * edist z w := by
    obtain ⟨K, hK⟩ := hLip n
    refine ⟨K, fun z w => ?_⟩
    rw [Metric.edistOf_restrictOpen_connCompOpen g (γ 0)]
    exact hK z w
  have htraceC (n : ℕ) : diskTrace (uC n) = (loopInComponent γ).comp (τ n) :=
    diskInLoopComponent_trace γ (τ n) (u n) (htrace n)
  have hEC (n : ℕ) (z : ℂ) : diskMapEnergyDensity gC (diskExtension (uC n)) z =
      diskMapEnergyDensity g (diskExtension (u n)) z :=
    diskMapEnergyDensity_restrictOpen g C (diskExtension (uC n)) z
  have hEInt (n : ℕ) : (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity gC (diskExtension (uC n)) z) =
      ∫ z in closedBall (0 : ℂ) 1, diskMapEnergyDensity g (diskExtension (u n)) z :=
    integral_congr_ae (Eventually.of_forall (hEC n))
  have henergyC (n : ℕ) : (∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity gC (diskExtension (uC n)) z) ≤ A := by
    rw [hEInt n]
    exact henergy n
  obtain ⟨φ, v, hφ, hvm, hv⟩ :=
    exists_aemeasurable_ae_tendsto_subseq_of_disk_energy_bounded gC hgC (loopInComponent γ)
      uC hLipC (fun n => ⟨τ n, htraceC n⟩) henergyC
  obtain ⟨ι, hι, center, χ, ρ, hρc, hρsupport, hw, hD0, hDInt, hDle⟩ :=
    exists_chart_partition_energy_density_le_liminf gC L (fun n => uC (φ n)) v
      (fun n => hLipC (φ n)) hv (fun n => henergyC (φ n))
  have hlim : Tendsto (fun n => ∫ z in closedBall (0 : ℂ) 1,
      diskMapEnergyDensity gC (diskExtension (uC (φ n))) z) atTop (𝓝 b) := by
    simpa only [Function.comp_def, hEInt] using henergyLim.comp hφ.tendsto_atTop
  rw [hlim.liminf_eq] at hDle
  refine ⟨φ, v, hφ, hvm, hUC, hEC, fun n => htraceC (φ n), hv, ?_,
    ι, hι, center, χ, ρ, hρc, hρsupport, hw, hD0, hDInt, hDle⟩
  filter_upwards [hv] with z hz
  exact (continuous_subtype_val.tendsto (v z)).comp hz

end DifferentialGeometry.Geometry

end

end
