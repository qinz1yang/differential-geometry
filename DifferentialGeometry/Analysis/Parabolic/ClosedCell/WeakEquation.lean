import DifferentialGeometry.Analysis.Elliptic.MetricExtension.ClosedCellAffineDensity
import DifferentialGeometry.Analysis.Parabolic.WeakEquation.AffineLpTransport

noncomputable section

open Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold Matrix Topology

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.Topology.Handle

private local instance (m : ℕ) :
    ChartedSpace (EuclideanHalfSpace (m + 1)) (ClosedCell (m + 1)) :=
  closedCellChartedSpaceSucc m

private local instance (m : ℕ) :
    IsManifold (𝓡∂ (m + 1)) ∞ (ClosedCell (m + 1)) :=
  closedCellIsManifold m

variable {m : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "V" => EuclideanSpace ℝ (Fin (m + 1))
local notation "W" => EuclideanSpace ℝ (Fin (Module.finrank ℝ V))

private local instance : T2Space V := inferInstance

theorem exists_closedCell_lp_weighted_weak_equation
    (D : RealTimeInterval) (g : ℝ → SmoothRiemannianMetric I M)
    (Φ : PartialDiffeomorph (𝓡 (m + 1)) I V M ∞)
    (c : V) {r : ℝ} (hr : 0 < r)
    (hsource : Metric.closedBall c r ⊆ Φ.source)
    (α : ClosedCell (m + 1)) (hα : ‖α.val‖ < 1)
    (μ : Measure ℝ) [SFinite μ] (J : Set ℝ) (Ω : Set W) :
    let b : W := (toEuclidean (E := V)) c -
      r • (toEuclidean (E := V)) (EuclideanSpace.basisFun (Fin (m + 1)) ℝ 0)
    let Ψ : W → M := fun z => Φ ((toEuclidean (E := V)).symm z)
    let Q : ℝ × W → Matrix (Fin (Module.finrank ℝ V)) (Fin (Module.finrank ℝ V)) ℝ :=
      fun q => Matrix.of (fun i j => pullbackMetricCoefficients (g q.1) Ψ q.2
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
    ((fun x => b + r • x) ⁻¹' Ω ⊆
      toEuclidean (E := V) '' interior (extChartAt (𝓡∂ (m + 1)) α).target) →
    ∀ {p : ℝ≥0∞} (U F : Lp ℝ p (μ.prod (volume.restrict Ω)))
      (K : Fin (Module.finrank ℝ V) → Lp ℝ p (μ.prod (volume.restrict Ω))),
      (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
        (fun x => K k (t, x)) (fun x => U (t, x)) Ω) →
      (∀ φ : ℝ × W → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
        HasCompactSupport φ → tsupport φ ⊆ J ×ˢ Ω →
        (∫ q, Real.sqrt (Q q).det * U q * fderiv ℝ φ q (1, 0)
          ∂μ.prod (volume.restrict Ω)) =
          (∑ j, ∫ q, (∑ i, (Real.sqrt (Q q).det * (Q q)⁻¹ i j) * K i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂μ.prod (volume.restrict Ω)) -
          ∫ q, F q * φ q ∂μ.prod (volume.restrict Ω)) →
      let ν := μ.prod (volume.restrict ((fun x => b + r • x) ⁻¹' Ω))
      ∃ Uh Fh : Lp ℝ p ν, ∃ Kh : Fin (Module.finrank ℝ V) → Lp ℝ p ν,
        (Uh =ᵐ[ν] fun q => U (q.1, b + r • q.2)) ∧
        (Fh =ᵐ[ν] fun q => r ^ Module.finrank ℝ V * F (q.1, b + r • q.2)) ∧
        (∀ i, Kh i =ᵐ[ν] fun q => r * K i (q.1, b + r • q.2)) ∧
        (∀ k, ∀ᵐ t ∂μ, DeGiorgi.HasWeakPartialDeriv k
          (fun x => Kh k (t, x)) (fun x => Uh (t, x))
          ((fun x => b + r • x) ⁻¹' Ω)) ∧
        ∀ φ : ℝ × W → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
          HasCompactSupport φ → tsupport φ ⊆ J ×ˢ ((fun x => b + r • x) ⁻¹' Ω) →
          (∫ q, MetricExtension.densityOnEuclid
              ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric q.1) α q.2 *
            Uh q * fderiv ℝ φ q (1, 0) ∂ν) =
            (∑ j, ∫ q, (∑ i, MetricExtension.weightedInvGramOnEuclid
                ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric q.1) α i j q.2 *
              Kh i q) * fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν) -
            ∫ q, Fh q * φ q ∂ν := by
  intro b Ψ Q hΩ p U F K hspatial hweak ν
  let ρ : ℝ × W → ℝ := fun q => Real.sqrt (Q q).det
  let A := fun i j (q : ℝ × W) => Real.sqrt (Q q).det * (Q q)⁻¹ i j
  let S : ℝ × W → ℝ × W := fun q => (q.1, b + r • q.2)
  let δ := |r ^ Module.finrank ℝ V|
  have hδ : δ = r ^ Module.finrank ℝ V := abs_of_pos (pow_pos hr _)
  obtain ⟨Uh, Fh, Kh, hU, hF, hK, hspatialH, hweakH⟩ :=
    exists_lp_weighted_weak_equation_comp_add_smul μ J Ω ρ A U F K
      hspatial hweak b hr.ne'
  refine ⟨Uh, Fh, Kh, hU, ?_, hK, hspatialH, ?_⟩
  · simpa only [abs_of_pos (pow_pos hr _)] using hF
  · intro φ hφ hφc hφs
    have hρ (q : ℝ × W) (hq : q.2 ∈ (fun x => b + r • x) ⁻¹' Ω) :
        MetricExtension.densityOnEuclid
            ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric q.1) α q.2 =
          δ * ρ (S q) := by
      rw [hδ]
      exact MetricExtension.densityOnEuclid_closedCellPullbackMetricFamily_affine
        D g Φ c hr hsource q.1 α hα (hΩ hq)
    have hA (q : ℝ × W) (hq : q.2 ∈ (fun x => b + r • x) ⁻¹' Ω)
        (i j : Fin (Module.finrank ℝ V)) :
        MetricExtension.weightedInvGramOnEuclid
            ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric q.1) α i j q.2 =
          (δ / r ^ 2) * A i j (S q) := by
      rw [hδ]
      exact MetricExtension.weightedInvGramOnEuclid_closedCellPullbackMetricFamily_affine
        D g Φ c hr hsource q.1 α hα (hΩ hq) i j
    have hzero (q : ℝ × W) (hq : q.2 ∉ (fun x => b + r • x) ⁻¹' Ω)
        (v : ℝ × W) : fderiv ℝ φ q v = 0 :=
      image_eq_zero_of_notMem_tsupport (f := fun x : ℝ × W => fderiv ℝ φ x v)
        (fun h => hq (hφs ((tsupport_fderiv_apply_subset ℝ v) h)).2)
    have hleft :
        (∫ q, MetricExtension.densityOnEuclid
            ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric q.1) α q.2 *
          Uh q * fderiv ℝ φ q (1, 0) ∂ν) =
          ∫ q, (δ * ρ (S q)) * Uh q * fderiv ℝ φ q (1, 0) ∂ν := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun q => ?_
      dsimp only
      by_cases hq : q.2 ∈ (fun x => b + r • x) ⁻¹' Ω
      · rw [hρ q hq]
      · simp only [hzero q hq (1, 0), mul_zero]
    have hright (j : Fin (Module.finrank ℝ V)) :
        (∫ q, (∑ i, MetricExtension.weightedInvGramOnEuclid
            ((closedCellPullbackMetricFamily D g Φ c hr hsource).metric q.1) α i j q.2 *
          Kh i q) * fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν) =
          ∫ q, (∑ i, (δ / r ^ 2 * A i j (S q)) * Kh i q) *
            fderiv ℝ φ q (0, EuclideanSpace.single j 1) ∂ν := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun q => ?_
      dsimp only
      by_cases hq : q.2 ∈ (fun x => b + r • x) ⁻¹' Ω
      · simp only [hA q hq]
      · simp only [hzero q hq (0, EuclideanSpace.single j 1), mul_zero]
    rw [hleft]
    simp only [hright]
    exact hweakH φ hφ hφc hφs

end DifferentialGeometry.Analysis.Parabolic
