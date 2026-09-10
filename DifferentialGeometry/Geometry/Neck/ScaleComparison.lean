import DifferentialGeometry.Geometry.Neck.Chart
import DifferentialGeometry.Geometry.Curvature.ScalarTrace

noncomputable section
open Set
open scoped Manifold ContDiff BigOperators
open DifferentialGeometry DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open Poincare.Geometry.Metric Poincare.Geometry.Curvature

namespace Poincare.Geometry.Neck

private abbrev S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

private theorem abs_trace_le_of_metric_bound
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SmoothRiemannianMetric I M) (x : M)
    (A : TangentSpace I x →ₗ[ℝ] TangentSpace I x) (c : ℝ)
    (hA : ∀ v, Real.sqrt (g.inner x (A v) (A v)) ≤ c * Real.sqrt (g.inner x v v)) :
    |LinearMap.trace ℝ (TangentSpace I x) A| ≤ (Module.finrank ℝ E : ℝ) * c := by
  sorry

private theorem trace_restricted_roundCylinder (O : TopologicalSpace.Opens (S × ℝ)) (x : O) :
    LinearMap.trace ℝ (TangentSpace IC x)
      (ricciSharp ((roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen O)
        x).toLinearMap = 1 := by
  have he : (ricciSharp
      ((roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen O)
      x).toLinearMap =
      LinearMap.prodMap ((1 / 2 : ℝ) •
        (LinearMap.id : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)))
        (0 : ℝ →ₗ[ℝ] ℝ) := by
    ext v
    change ricciSharp
      ((roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen O) x v =
        ((1 / 2 : ℝ) • v.1, (0 : ℝ))
    convert ricciSharp_restricted_roundCylinder O x v using 1
    norm_num
  have ht := congrArg (LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)) he
  refine ht.trans ?_
  rw [LinearMap.trace_prodMap', map_smul, LinearMap.trace_id, map_zero]
  norm_num

private theorem trace_restricted_roundCylinder_sub_one_le
    (O : TopologicalSpace.Opens (S × ℝ)) (g : SmoothRiemannianMetric IC O)
    (x : O) (ε : ℝ) (hε : ε ≤ 1 / 2)
    (hsmall : ∀ k : ℕ, k ≤ 2 → metricDerivNorm k g
      ((roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen O)
      ((roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen O) x ≤ ε) :
    |LinearMap.trace ℝ (TangentSpace IC x) (ricciSharp g x).toLinearMap - 1| ≤ 4323 * ε := by
  let gRef := (roundCylinderMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).restrictOpen O
  have h := abs_trace_le_of_metric_bound gRef x
    ((ricciSharp g x).toLinearMap - (ricciSharp gRef x).toLinearMap) (1441 * ε)
    (ricciSharp_restricted_roundCylinder_difference_bound O g x ε hε hsmall)
  rw [map_sub, trace_restricted_roundCylinder O x] at h
  convert h using 1
  norm_num
  ring

private theorem trace_ricciSharp_pullback
    {E F H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
    [BoundarylessManifold I M] [BoundarylessManifold J N]
    (g : SmoothRiemannianMetric J N) (Φ : M ≃ₘ⟮I, J⟯ N) (x : M) :
    LinearMap.trace ℝ (TangentSpace I x)
      (ricciSharp (Diffeomorph.pullbackMetricCross g Φ) x).toLinearMap =
        LinearMap.trace ℝ (TangentSpace J (Φ x)) (ricciSharp g (Φ x)).toLinearMap := by
  let e := Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have he (z : TangentSpace I x) : e z = mfderiv I J Φ x z :=
    congrArg (fun A : TangentSpace I x →L[ℝ] TangentSpace J (Φ x) ↦ A z)
      (Φ.mfderivToContinuousLinearEquiv_coe (by decide))
  let A := (ricciSharp g (Φ x)).toLinearMap
  have hconj : (ricciSharp (Diffeomorph.pullbackMetricCross g Φ) x).toLinearMap =
      e.toLinearEquiv.symm.conj A := by
    apply LinearMap.ext
    intro v
    apply e.injective
    change e (ricciSharp (Diffeomorph.pullbackMetricCross g Φ) x v) = e (e.symm (A (e v)))
    rw [e.apply_symm_apply, he, he]
    exact ricciSharp_pullbackMetricCross g Φ x v
  rw [hconj]
  exact LinearMap.trace_conj' A e.toLinearEquiv.symm

variable {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
  [BoundarylessManifold J M]

theorem cylindricalChart.scalar_comparison_of_metricCloseOn
    (C : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    {U : Set C.domain} (ε : ℝ) (hε : ε ≤ 1 / 2) (hsmall : C.metricCloseOn g ε U)
    (y : M) (hy : y ∈ C.region U) :
    |metricScalarAt g y / C.scale - 1| ≤ 4323 * ε := by
  rcases hy with ⟨z, ⟨x, hx, rfl⟩, rfl⟩
  let : SigmaCompactSpace C.domain := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC C.domain.isOpen)
  have hrange : range (C.chart : C.domain → C.target) = univ := C.chart.surjective.range_eq
  let : SigmaCompactSpace C.target := isSigmaCompact_univ_iff.mp
    (hrange ▸ isSigmaCompact_range C.chart.continuous)
  let e := C.chart.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have hdim : Module.finrank ℝ F = 3 := by
    have h := e.toLinearEquiv.finrank_eq
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × ℝ) = Module.finrank ℝ F at h
    simpa using h.symm
  let : NeZero (Module.finrank ℝ F) := ⟨by rw [hdim]; norm_num⟩
  let gV := g.restrictOpen C.target
  have hscale : (ricciSharp (scaleMetric C.scale C.scale_pos gV) (C.chart x)).toLinearMap =
      C.scale⁻¹ • (ricciSharp gV (C.chart x)).toLinearMap := by
    ext v
    exact ricciSharp_scaleMetric gV C.scale C.scale_pos (C.chart x) v
  have hrestrict : (ricciSharp gV (C.chart x)).toLinearMap =
      (ricciSharp g (C.chart x : M)).toLinearMap := by
    ext v
    have h := ricciSharp_restrictOpen g C.target (C.chart x) v
    rw [mfderiv_subtype_val] at h
    exact h
  have h := trace_restricted_roundCylinder_sub_one_le C.domain
    (Diffeomorph.pullbackMetricCross (scaleMetric C.scale C.scale_pos gV) C.chart)
    x ε hε (hsmall x hx)
  rw [trace_ricciSharp_pullback, hscale, map_smul, hrestrict] at h
  rw [metricScalar_eq_trace_ricciSharp g (C.chart x : M)]
  change |C.scale⁻¹ * LinearMap.trace ℝ F (ricciSharp g (C.chart x : M)).toLinearMap - 1| ≤
    4323 * ε at h
  change |LinearMap.trace ℝ F (ricciSharp g (C.chart x : M)).toLinearMap / C.scale - 1| ≤
    4323 * ε
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using h

private theorem abs_ratio_sub_one_le_of_common_normalization
    (R Q₀ Q₁ η : ℝ) (hQ₀ : 0 < Q₀) (hQ₁ : 0 < Q₁) (hη : η ≤ 1 / 2)
    (h₀ : |R / Q₀ - 1| ≤ η) (h₁ : |R / Q₁ - 1| ≤ η) :
    |Q₀ / Q₁ - 1| ≤ 4 * η := by
  have hlow : 1 / 2 ≤ R / Q₀ := by
    have h := (abs_le.mp h₀).1
    linarith only [h, hη]
  have hid : (R / Q₀) * (Q₀ / Q₁ - 1) = (R / Q₁ - 1) - (R / Q₀ - 1) := by
    field_simp
    ring
  have hdiff : |(R / Q₀) * (Q₀ / Q₁ - 1)| ≤ 2 * η := by
    rw [hid]
    exact (abs_sub _ _).trans (by linarith only [h₀, h₁])
  rw [abs_mul, abs_of_pos (lt_of_lt_of_le (by norm_num) hlow)] at hdiff
  have hprod := mul_le_mul_of_nonneg_right hlow (abs_nonneg (Q₀ / Q₁ - 1))
  linarith only [hdiff, hprod]

theorem cylindricalChart.scale_ratio_of_metricCloseOn
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    {U₀ : Set C₀.domain} {U₁ : Set C₁.domain}
    (ε : ℝ) (hε : ε < 1 / 200000)
    (h₀ : C₀.metricCloseOn g ε U₀) (h₁ : C₁.metricCloseOn g ε U₁)
    (y : M) (hy₀ : y ∈ C₀.region U₀) (hy₁ : y ∈ C₁.region U₁) :
    |C₀.scale / C₁.scale - 1| ≤ 17292 * ε := by
  have hsmall : ε ≤ 1 / 2 := by linarith only [hε]
  have h := abs_ratio_sub_one_le_of_common_normalization (metricScalarAt g y)
    C₀.scale C₁.scale (4323 * ε) C₀.scale_pos C₁.scale_pos (by linarith only [hε])
    (C₀.scalar_comparison_of_metricCloseOn g ε hsmall h₀ y hy₀)
    (C₁.scalar_comparison_of_metricCloseOn g ε hsmall h₁ y hy₁)
  convert h using 1
  ring

end Poincare.Geometry.Neck
