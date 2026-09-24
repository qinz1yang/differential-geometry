import DifferentialGeometry.Geometry.Coordinates.Isothermal.PullbackConductivity
import DifferentialGeometry.Geometry.Measure.Area.Regularization
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Reparametrization.RegularizedMetric
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import DifferentialGeometry.Analysis.Elliptic.Planar.Conductivity.Univalent

section

noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Topology
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem SmoothDiskExtension.exists_regularized_metric_dirichlet_stream
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ω : TopologicalSpace.Opens ℂ) (δ r R : ℝ)
      (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω)
      (B : SmoothEllipticBilinearForm 2 (univ : Set V))
      (A : DeGiorgi.EllipticCoeff 2 (Metric.ball (0 : V) R)) (u v s : V → ℝ),
      0 < δ ∧ 1 < r ∧ r < R ∧ Metric.closedBall (0 : ℂ) R ⊆ Ω ∧
      (∀ (x : Ω) (ξ ζ : ℂ), h.inner x ξ ζ =
        pullbackMetricCoefficients g Q x.1 ξ ζ + δ * inner ℝ ξ ζ) ∧
      (∀ (x : Ω) (ξ : ℂ), δ * ‖ξ‖ ^ 2 ≤ h.inner x ξ ξ) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, regularizedPullbackAreaDensity g Q δ z) <
        riemannianDiskArea g q + ε ∧
      A.a = B.a ∧ B.c = 0 ∧
      (∀ x ∈ Metric.closedBall (0 : V) R,
        A.a x = pullbackConductivity g Q δ (Complex.orthonormalBasisOneI.repr.symm x)) ∧
      DeGiorgi.IsHomogeneousWeakSolution A u ∧
      DeGiorgi.MemW01p 2 (fun x => u x - x 0) (Metric.ball (0 : V) R) ∧
      ContDiffOn ℝ ∞ v (Metric.ball (0 : V) r) ∧
      ContDiffOn ℝ ∞ s (Metric.ball (0 : V) r) ∧
      u =ᵐ[volume.restrict (Metric.ball (0 : V) r)] v ∧
      (∀ x ∈ Metric.ball (0 : V) r,
        HasFDerivAt s
          (planarFluxForm (fun y => DeGiorgi.matMulE (A.a y) (DeGiorgi.smoothGradField v y)) x) x) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) r,
        complexAntilinearPart (fderiv ℝ (fun w =>
          (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
            (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z) =
          pullbackBeltramiCoefficient g Q δ z * complexLinearPart (fderiv ℝ (fun w =>
            (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
              (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z) := by
  obtain ⟨heq, N, hN, hDN, hQs⟩ := hQ
  let Ω : TopologicalSpace.Opens ℂ := ⟨N, hN⟩
  obtain ⟨δ, h, hδ, hinner, hbound, harea⟩ :=
    exists_regularized_pullback_disk_metric_area_lt g Ω hQs hDN hε
  obtain ⟨η, hη, hsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hN hDN
  have hball : Metric.closedBall (0 : ℂ) (η + 1) ⊆ N := by
    simpa only [cthickening_closedBall hη.le (zero_le_one' ℝ)] using hsub
  have hr : 0 < η / 2 + 1 := by positivity
  have hrR : η / 2 + 1 < η + 1 := by linarith
  have hh := exists_dirichlet_stream_pullbackConductivity g hN hQs hδ hr hrR hball
  have hz : Complex.orthonormalBasisOneI.repr (0 : ℂ) = 0 := map_zero _
  rw [hz] at hh
  obtain ⟨B, A, u, v, s, hAB, hBc, hA, hu, ht, hv, hs, huv, hds, hBel⟩ := hh
  refine ⟨Ω, δ, η / 2 + 1, η + 1, h, B, A, u, v, s, hδ, by linarith,
    hrR, hball, hinner, hbound, ?_, hAB, hBc, hA, hu, ht, hv, hs, huv, hds, hBel⟩
  simpa only [riemannianDiskArea_eq_of_extension g q Q heq] using harea

end DifferentialGeometry.Geometry

end

end

section

noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Topology
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem SmoothDiskExtension.exists_regularized_metric_positive_jacobian_stream
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ω : TopologicalSpace.Opens ℂ) (δ r R : ℝ)
      (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω)
      (B : SmoothEllipticBilinearForm 2 (univ : Set V))
      (A : DeGiorgi.EllipticCoeff 2 (Metric.ball (0 : V) R)) (u v s : V → ℝ),
      0 < δ ∧ 1 < r ∧ r < R ∧ Metric.closedBall (0 : ℂ) R ⊆ Ω ∧
      (∀ (x : Ω) (ξ ζ : ℂ), h.inner x ξ ζ =
        pullbackMetricCoefficients g Q x.1 ξ ζ + δ * inner ℝ ξ ζ) ∧
      (∀ (x : Ω) (ξ : ℂ), δ * ‖ξ‖ ^ 2 ≤ h.inner x ξ ξ) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, regularizedPullbackAreaDensity g Q δ z) <
        riemannianDiskArea g q + ε ∧
      A.a = B.a ∧ B.c = 0 ∧
      (∀ x ∈ Metric.closedBall (0 : V) R,
        A.a x = pullbackConductivity g Q δ (Complex.orthonormalBasisOneI.repr.symm x)) ∧
      DeGiorgi.IsHomogeneousWeakSolution A u ∧
      DeGiorgi.MemW01p 2 (fun x => u x - x 0) (Metric.ball (0 : V) R) ∧
      ContDiffOn ℝ ∞ v (Metric.ball (0 : V) r) ∧
      ContDiffOn ℝ ∞ s (Metric.ball (0 : V) r) ∧
      u =ᵐ[volume.restrict (Metric.ball (0 : V) r)] v ∧
      (∀ x ∈ Metric.ball (0 : V) r,
        HasFDerivAt s
          (planarFluxForm (fun y => DeGiorgi.matMulE (A.a y) (DeGiorgi.smoothGradField v y)) x) x) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r,
        0 < (fderiv ℝ (fun w =>
          (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
            (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z).toLinearMap.det) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) r,
        complexAntilinearPart (fderiv ℝ (fun w =>
          (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
            (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z) =
          pullbackBeltramiCoefficient g Q δ z * complexLinearPart (fderiv ℝ (fun w =>
            (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
              (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z) := by
  obtain ⟨Ω, δ, r, R, h, B, A, u, v, s, hδ, hr, hrR, hball,
    hinner, hbound, harea, hAB, hBc, hA, hu, ht, hv, hs, huv, hds, hBel⟩ :=
    hQ.exists_regularized_metric_dirichlet_stream g hε
  have hdet (x : V) (hx : x ∈ Metric.ball (0 : V) R) : (A.a x).det = 1 := by
    rw [hA x (Metric.ball_subset_closedBall hx)]
    exact det_pullbackConductivity g Q hδ _
  have hsol := DeGiorgi.isHomogeneousWeakSolution_isSolution hu
  have hJ := hsol.det_fderiv_pos_of_coordinate_trace_stream (zero_lt_one.trans hr) hrR.le B
      (fun x _ => congrFun hAB x) hdet ht hv.continuousOn huv hds
  exact ⟨Ω, δ, r, R, h, B, A, u, v, s, hδ, hr, hrR, hball, hinner, hbound, harea,
    hAB, hBc, hA, hu, ht, hv, hs, huv, hds, hJ, hBel⟩

end DifferentialGeometry.Geometry

end

end

section

noncomputable section
open Set Filter MeasureTheory Manifold
open DifferentialGeometry.Topology
open scoped ContDiff ENNReal Manifold

namespace DifferentialGeometry.Geometry
open DifferentialGeometry.Analysis
open DifferentialGeometry.Analysis.Sobolev.NirenbergEuclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
local notation "V" => EuclideanSpace ℝ (Fin 2)

theorem SmoothDiskExtension.exists_regularized_metric_injective_stream
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {q : C(closedDisk, M)} {Q : ℂ → M} (hQ : SmoothDiskExtension (E := E) q Q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (Ω : TopologicalSpace.Opens ℂ) (δ r R : ℝ)
      (h : SmoothRiemannianMetric 𝓘(ℝ, ℂ) Ω)
      (B : SmoothEllipticBilinearForm 2 (univ : Set V))
      (A : DeGiorgi.EllipticCoeff 2 (Metric.ball (0 : V) R)) (u v s : V → ℝ),
      0 < δ ∧ 1 < r ∧ r < R ∧ Metric.closedBall (0 : ℂ) R ⊆ Ω ∧
      (∀ (x : Ω) (ξ ζ : ℂ), h.inner x ξ ζ =
        pullbackMetricCoefficients g Q x.1 ξ ζ + δ * inner ℝ ξ ζ) ∧
      (∀ (x : Ω) (ξ : ℂ), δ * ‖ξ‖ ^ 2 ≤ h.inner x ξ ξ) ∧
      (∫ z in Metric.closedBall (0 : ℂ) 1, regularizedPullbackAreaDensity g Q δ z) <
        riemannianDiskArea g q + ε ∧
      A.a = B.a ∧ B.c = 0 ∧
      (∀ x ∈ Metric.closedBall (0 : V) R,
        A.a x = pullbackConductivity g Q δ (Complex.orthonormalBasisOneI.repr.symm x)) ∧
      DeGiorgi.IsHomogeneousWeakSolution A u ∧
      DeGiorgi.MemW01p 2 (fun x => u x - x 0) (Metric.ball (0 : V) R) ∧
      ContDiffOn ℝ ∞ v (Metric.ball (0 : V) r) ∧
      ContDiffOn ℝ ∞ s (Metric.ball (0 : V) r) ∧
      u =ᵐ[volume.restrict (Metric.ball (0 : V) r)] v ∧
      (∀ x ∈ Metric.ball (0 : V) r,
        HasFDerivAt s
          (planarFluxForm (fun y => DeGiorgi.matMulE (A.a y) (DeGiorgi.smoothGradField v y)) x) x) ∧
      InjOn (fun w => (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
        (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) (Metric.ball (0 : ℂ) r) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) r,
        0 < (fderiv ℝ (fun w =>
          (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
            (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z).toLinearMap.det) ∧
      ∀ z ∈ Metric.ball (0 : ℂ) r,
        complexAntilinearPart (fderiv ℝ (fun w =>
          (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
            (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z) =
          pullbackBeltramiCoefficient g Q δ z * complexLinearPart (fderiv ℝ (fun w =>
            (v (Complex.orthonormalBasisOneI.repr w) : ℂ) +
              (s (Complex.orthonormalBasisOneI.repr w) : ℂ) * Complex.I) z) := by
  obtain ⟨Ω, δ, r, R, h, B, A, u, v, s, hδ, hr, hrR, hball,
    hinner, hbound, harea, hAB, hBc, hA, hu, ht, hv, hs, huv, hds, hJ, hBel⟩ :=
    hQ.exists_regularized_metric_positive_jacobian_stream g hε
  have hdet (x : V) (hx : x ∈ Metric.ball (0 : V) R) : (A.a x).det = 1 := by
    rw [hA x (Metric.ball_subset_closedBall hx)]
    exact det_pullbackConductivity g Q hδ _
  have hsol := DeGiorgi.isHomogeneousWeakSolution_isSolution hu
  have hinj := hsol.injOn_complex_stream_of_coordinate_trace (zero_lt_one.trans hr) hrR.le B
    (fun x _ => congrFun hAB x) hdet ht hv.continuousOn huv hds
  exact ⟨Ω, δ, r, R, h, B, A, u, v, s, hδ, hr, hrR, hball, hinner, hbound, harea,
    hAB, hBc, hA, hu, ht, hv, hs, huv, hds, hinj, hJ, hBel⟩

end DifferentialGeometry.Geometry

end

end
