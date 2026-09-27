import DifferentialGeometry.Analysis.Elliptic.MetricExtension
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensity

noncomputable section

open Manifold Set
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

omit [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] in
private lemma chart_inverse_mem_source (α : M) {z : EuclN}
    (hz : z ∈ chartTargetEuclid (I := I) α) :
    (extChartAt I α).symm ((toEuclidean (E := E)).symm z) ∈ (chartAt H α).source := by
  rw [← extChartAt_source_eq_chartAt_source (I := I)]
  exact (extChartAt I α).map_target (toEuclidean_symm_mem_target hz)

lemma riemannianVolumeDensity_mul_chartInverse_eq_inv_densityOnEuclid
    (q h : SmoothRiemannianMetric I M) (α : M) {Ω : Set EuclN}
    (hΩs : Ω ⊆ chartTargetEuclid (I := I) α) (φ : C^∞⟮I, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = 1) :
    let P := fun z => (riemannianVolumeDensitySmoothMap h q * φ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    EqOn P (fun z => (densityOnEuclid h α z)⁻¹) Ω := by
  intro P z hz
  exact riemannianVolumeDensity_mul_eq_inv_chartDensity q h α
    (chart_inverse_mem_source α (hΩs hz)) (hφ z hz)

lemma densityOnEuclid_mul_riemannianVolumeDensity_mul_chartInverse
    (q h : SmoothRiemannianMetric I M) (α : M) {Ω : Set EuclN}
    (hΩs : Ω ⊆ chartTargetEuclid (I := I) α) (φ : C^∞⟮I, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = 1) :
    let P := fun z => (riemannianVolumeDensitySmoothMap h q * φ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    ∀ z ∈ Ω, densityOnEuclid h α z * P z = 1 := by
  intro P z hz
  have heq : P z = (densityOnEuclid h α z)⁻¹ :=
    riemannianVolumeDensity_mul_chartInverse_eq_inv_densityOnEuclid q h α hΩs φ hφ hz
  rw [heq]
  exact mul_inv_cancel₀ (ne_of_gt (chartDensity_pos h α (chart_inverse_mem_source α (hΩs hz))))

lemma riemannianVolumeDensity_mul_chartInverse_pos
    (q h : SmoothRiemannianMetric I M) (α : M) {Ω : Set EuclN}
    (hΩs : Ω ⊆ chartTargetEuclid (I := I) α) (φ : C^∞⟮I, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = 1) :
    let P := fun z => (riemannianVolumeDensitySmoothMap h q * φ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    ∀ z ∈ Ω, 0 < P z := by
  intro P z hz
  have heq : P z = (densityOnEuclid h α z)⁻¹ :=
    riemannianVolumeDensity_mul_chartInverse_eq_inv_densityOnEuclid q h α hΩs φ hφ hz
  rw [heq]
  exact inv_pos.mpr (chartDensity_pos h α (chart_inverse_mem_source α (hΩs hz)))

lemma weightedInvGramOnEuclid_mul_riemannianVolumeDensity_mul_chartInverse
    (q h : SmoothRiemannianMetric I M) (α : M) {Ω : Set EuclN}
    (hΩs : Ω ⊆ chartTargetEuclid (I := I) α) (φ : C^∞⟮I, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = 1)
    (i j : Fin (Module.finrank ℝ E)) :
    let P := fun z => (riemannianVolumeDensitySmoothMap h q * φ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    ∀ z ∈ Ω, weightedInvGramOnEuclid h α i j z * P z = invGramOnEuclid h α i j z := by
  intro P z hz
  calc
    _ = (densityOnEuclid h α z * P z) * invGramOnEuclid h α i j z := by
      dsimp only [weightedInvGramOnEuclid]
      ring
    _ = _ := by rw [densityOnEuclid_mul_riemannianVolumeDensity_mul_chartInverse q h α hΩs φ hφ z hz, one_mul]

lemma fderiv_riemannianVolumeDensity_mul_chartInverse
    (q h : SmoothRiemannianMetric I M) (α : M) {Ω : Set EuclN}
    (hΩ : IsOpen Ω) (hΩs : Ω ⊆ chartTargetEuclid (I := I) α) (φ : C^∞⟮I, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, densityOnEuclid q α z *
      φ ((extChartAt I α).symm ((toEuclidean (E := E)).symm z)) = 1) :
    let P := fun z => (riemannianVolumeDensitySmoothMap h q * φ)
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm z))
    ∀ z ∈ Ω, fderiv ℝ P z = -(P z ^ 2) • fderiv ℝ (densityOnEuclid h α) z := by
  intro P z hz
  have heq : EqOn P (fun z => (densityOnEuclid h α z)⁻¹) Ω :=
    riemannianVolumeDensity_mul_chartInverse_eq_inv_densityOnEuclid q h α hΩs φ hφ
  have hd : DifferentiableAt ℝ (densityOnEuclid h α) z :=
    ((densityOnEuclid_contDiffOn h α).mono hΩs).contDiffAt (hΩ.mem_nhds hz) |>.differentiableAt (by simp)
  have hρ : densityOnEuclid h α z ≠ 0 :=
    ne_of_gt (chartDensity_pos h α (chart_inverse_mem_source α (hΩs hz)))
  rw [(heq.eventuallyEq_of_mem (hΩ.mem_nhds hz)).fderiv_eq]
  have hinv : fderiv ℝ (fun z => (densityOnEuclid h α z)⁻¹) z =
      -(densityOnEuclid h α z ^ 2)⁻¹ • fderiv ℝ (densityOnEuclid h α) z :=
    ((hasDerivAt_inv hρ).comp_hasFDerivAt z hd.hasFDerivAt).fderiv
  rw [hinv, heq hz, inv_pow]

end DifferentialGeometry.Analysis.Laplacian.MetricExtension

noncomputable section

namespace DifferentialGeometry.Analysis.Laplacian.MetricExtension

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

private lemma contDiffOn_smoothMap_chartInverse
    (α : M) {Ω : Set EuclN} (hΩs : Ω ⊆ chartTargetEuclid (I := I) α)
    (φ : C^∞⟮I, M; ℝ⟯) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => φ ((extChartAt I α).symm
      ((toEuclidean (E := E)).symm z))) Ω := by
  apply (scalarOnE_contDiffOn α φ.contMDiff).comp
    (toEuclidean (E := E)).symm.contDiff.contDiffOn
  intro z hz
  exact toEuclidean_symm_mem_target (hΩs hz)

lemma weightedInvGramOnEuclid_mul_fderiv_chartInverse_contDiffOn
    (g : SmoothRiemannianMetric I M) (α : M) {Ω : Set EuclN}
    (hΩ : IsOpen Ω) (hΩs : Ω ⊆ chartTargetEuclid (I := I) α)
    (φ : C^∞⟮I, M; ℝ⟯) (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => weightedInvGramOnEuclid g α i j z *
      fderiv ℝ (fun y => φ ((extChartAt I α).symm
        ((toEuclidean (E := E)).symm y))) z (EuclideanSpace.single j 1)) Ω := by
  exact ((weightedInvGramOnEuclid_contDiffOn g α i j).mono hΩs).mul
    (((contDiffOn_smoothMap_chartInverse α hΩs φ).fderiv_of_isOpen hΩ (by simp)).clm_apply contDiffOn_const)

end DifferentialGeometry.Analysis.Laplacian.MetricExtension
