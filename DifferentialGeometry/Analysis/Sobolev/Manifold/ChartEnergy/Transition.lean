import DifferentialGeometry.Analysis.Sobolev.Euclidean.CoordinateTransition
import DifferentialGeometry.Geometry.Coordinates.Chart.CompactTransition
import DifferentialGeometry.Analysis.Integration.Measure.OpenCover
import DifferentialGeometry.Topology.Homeomorph.SigmaCompact

section

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]

theorem gradient_energy_ae_eq_on_compact_chart_overlap
    {d m : ℕ} (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (g : SmoothRiemannianMetric I M)
    (ΦA ΦB : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    {K : Set M} (hK : IsCompact K) (hKA : K ⊆ ΦA.target) (hKB : K ⊆ ΦB.target)
    {χA χB : M → ℝ} (hχA : ∀ p ∈ K, χA p = 1) (hχB : ∀ p ∈ K, χB p = 1)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {v : EuclideanSpace ℝ (Fin d) → M} (hv : AEMeasurable v (volume.restrict Ω))
    (hA : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χA (v x) • ΦA.symm (v x)) i) Ω)
    (hB : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χB (v x) • ΦB.symm (v x)) i) Ω)
    {c : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hball : closedBall c r ⊆ Ω) :
    ∀ᵐ x ∂(volume.restrict (ball c r)).restrict (v ⁻¹' K), ∀ j : Fin d,
      pullbackMetricCoefficients g ΦB (ΦB.symm (v x))
        (L.symm (WithLp.toLp 2 (fun i => (hB i).weakGrad x j)))
        (L.symm (WithLp.toLp 2 (fun i => (hB i).weakGrad x j))) =
      pullbackMetricCoefficients g ΦA (ΦA.symm (v x))
        (L.symm (WithLp.toLp 2 (fun i => (hA i).weakGrad x j)))
        (L.symm (WithLp.toLp 2 (fun i => (hA i).weakGrad x j))) := by
  let : NormedAddCommGroup (EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  obtain ⟨R, hR, _, ⟨C, _, hC⟩, htrans⟩ :=
    exists_compactly_supported_chart_transition_pullback_metric L g ΦA ΦB hK hKA hKB
  let PA : M → EuclideanSpace ℝ (Fin m) := fun p => L (χA p • ΦA.symm p)
  let PB : M → EuclideanSpace ℝ (Fin m) := fun p => L (χB p • ΦB.symm p)
  let BA : M → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := fun p =>
    (pullbackMetricCoefficients g ΦA (ΦA.symm p)).bilinearComp
      L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
  let BB : M → EuclideanSpace ℝ (Fin m) →L[ℝ]
      EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ := fun p =>
    (pullbackMetricCoefficients g ΦB (ΦB.symm p)).bilinearComp
      L.symm.toContinuousLinearMap L.symm.toContinuousLinearMap
  have hvalue : ∀ p ∈ K, R (PA p) = PB p := by
    intro p hp
    simpa only [PA, PB, hχA p hp, hχB p hp, one_smul] using (htrans p hp).1
  have hmetric : ∀ p ∈ K, ∀ z : EuclideanSpace ℝ (Fin m),
      BB p (fderiv ℝ R (PA p) z) (fderiv ℝ R (PA p) z) = BA p z z := by
    intro p hp z
    simpa only [PA, BA, BB, ContinuousLinearMap.bilinearComp_apply,
      ContinuousLinearEquiv.coe_coe, hχA p hp, one_smul] using (htrans p hp).2 z z
  have h := Analysis.Sobolev.Euclidean.gradient_quadratic_ae_coordinate_transition_on_preimage
    (P := PA) (Q := PB) hΩ hv hK.measurableSet hA hB R
      (hR.of_le (by simp)) hC hvalue BA BB hmetric hball
  simpa only [BA, BB, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearEquiv.coe_coe] using h

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]

theorem gradient_energy_ae_eq_restrict_compact_chart_overlap
    {d m : ℕ} (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (g : SmoothRiemannianMetric I M)
    (ΦA ΦB : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    {K : Set M} (hK : IsCompact K) (hKA : K ⊆ ΦA.target) (hKB : K ⊆ ΦB.target)
    {χA χB : M → ℝ} (hχA : ∀ p ∈ K, χA p = 1) (hχB : ∀ p ∈ K, χB p = 1)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {v : EuclideanSpace ℝ (Fin d) → M} (hv : AEMeasurable v (volume.restrict Ω))
    (hA : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χA (v x) • ΦA.symm (v x)) i) Ω)
    (hB : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χB (v x) • ΦB.symm (v x)) i) Ω)
    : ∀ᵐ x ∂(volume.restrict Ω).restrict (v ⁻¹' K), ∀ j : Fin d,
      pullbackMetricCoefficients g ΦB (ΦB.symm (v x))
        (L.symm (WithLp.toLp 2 (fun i => (hB i).weakGrad x j)))
        (L.symm (WithLp.toLp 2 (fun i => (hB i).weakGrad x j))) =
      pullbackMetricCoefficients g ΦA (ΦA.symm (v x))
        (L.symm (WithLp.toLp 2 (fun i => (hA i).weakGrad x j)))
        (L.symm (WithLp.toLp 2 (fun i => (hA i).weakGrad x j))) := by
  rw [← Measure.restrict_comm hΩ.measurableSet]
  apply ae_restrict_of_ae_restrict_closedBall_subset hΩ
  intro c r hball
  rw [Measure.restrict_comm measurableSet_ball]
  exact gradient_energy_ae_eq_on_compact_chart_overlap L g ΦA ΦB hK hKA hKB
    hχA hχB hΩ hv hA hB hball

end DifferentialGeometry.Geometry

end

end

section

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [MeasurableSpace M] [BorelSpace M]

theorem gradient_energy_ae_eq_restrict_open_chart_overlap
    {d m : ℕ} (L : E ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (g : SmoothRiemannianMetric I M)
    (ΦA ΦB : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)
    {O : Set M} (hO : IsOpen O) (hOA : O ⊆ ΦA.target) (hOB : O ⊆ ΦB.target)
    {χA χB : M → ℝ} (hχA : ∀ p ∈ O, χA p = 1) (hχB : ∀ p ∈ O, χB p = 1)
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    {v : EuclideanSpace ℝ (Fin d) → M} (hv : AEMeasurable v (volume.restrict Ω))
    (hA : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χA (v x) • ΦA.symm (v x)) i) Ω)
    (hB : ∀ i : Fin m, DeGiorgi.MemW1pWitness 2
      (fun x => L (χB (v x) • ΦB.symm (v x)) i) Ω)
    : ∀ᵐ x ∂(volume.restrict Ω).restrict (v ⁻¹' O), ∀ j : Fin d,
      pullbackMetricCoefficients g ΦB (ΦB.symm (v x))
        (L.symm (WithLp.toLp 2 (fun i => (hB i).weakGrad x j)))
        (L.symm (WithLp.toLp 2 (fun i => (hB i).weakGrad x j))) =
      pullbackMetricCoefficients g ΦA (ΦA.symm (v x))
        (L.symm (WithLp.toLp 2 (fun i => (hA i).weakGrad x j)))
        (L.symm (WithLp.toLp 2 (fun i => (hA i).weakGrad x j))) := by
  let : FiniteDimensional ℝ E := L.symm.toLinearEquiv.finiteDimensional
  have hSigma : IsSigmaCompact O :=
    ΦA.toOpenPartialHomeomorph.isSigmaCompact_of_isOpen_subset_target hO hOA
  obtain ⟨K, hK, hcover⟩ := hSigma
  have hsub (n : ℕ) : K n ⊆ O := hcover ▸ subset_iUnion K n
  rw [← hcover, preimage_iUnion]
  apply (ae_restrict_iUnion_iff (fun n => v ⁻¹' K n) _).mpr
  intro n
  exact gradient_energy_ae_eq_restrict_compact_chart_overlap L g ΦA ΦB
    (hK n) ((hsub n).trans hOA) ((hsub n).trans hOB)
    (fun p hp => hχA p (hsub n hp)) (fun p hp => hχB p (hsub n hp))
    hΩ hv hA hB

end DifferentialGeometry.Geometry

end

end
