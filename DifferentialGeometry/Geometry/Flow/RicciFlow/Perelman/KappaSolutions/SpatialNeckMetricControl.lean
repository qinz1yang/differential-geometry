import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.SpatialNeck
import DifferentialGeometry.Geometry.Metric.Convergence.Metric.UniformEquivalence

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Manifold Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology

def spatialNeckControlEpsilon : ℝ := (100 * (1 + Real.pi))⁻¹

theorem spatialNeckControlEpsilon_pos : 0 < spatialNeckControlEpsilon := by
  dsimp only [spatialNeckControlEpsilon]
  positivity


theorem spatialNeckControlEpsilon_inverse_gap {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon) :
    5 * Real.pi + 12 * Real.pi < epsilon⁻¹ := by
  have hden : 0 < 100 * (1 + Real.pi) := by positivity
  have hprod : epsilon * (100 * (1 + Real.pi)) ≤ 1 := by
    apply (le_div_iff₀ hden).mp
    simpa only [spatialNeckControlEpsilon, inv_eq_one_div] using hsmall
  rw [inv_eq_one_div]
  apply (lt_div_iff₀ hepsilon).mpr
  nlinarith [mul_pos hepsilon Real.pi_pos]

private theorem spatialNeckControlEpsilon_le : spatialNeckControlEpsilon ≤ 23 / 144 := by
  have hden : 0 < 100 * (1 + Real.pi) := by positivity
  rw [spatialNeckControlEpsilon, inv_eq_one_div, div_le_iff₀ hden]
  nlinarith [Real.pi_pos]

universe u uE uH

private local instance spatialNeckControlSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance spatialNeckControlC1 : IsManifold I 1 N :=
  IsManifold.of_le (I := I) (M := N) (n := ∞) (by decide)

theorem SpatialNeckWitness.normalized_inner_bilipschitz
    {h : SmoothRiemannianMetric I N} {yStar : SpatialNeckSphere}
    {p : N} {epsilon : ℝ} (W : SpatialNeckWitness h yStar p epsilon)
    (hsmall : epsilon ≤ spatialNeckControlEpsilon)
    (x : spatialNeckBuffer epsilon) (hx : x ∈ spatialNeckClosedCore epsilon)
    (v : TangentSpace SpatialNeckCylinderModel x) :
    let gRef := unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)
    (11 / 12 : ℝ) ^ 2 * gRef.inner x v v ≤
        ((spatialNeckScale h p) ^ 2)⁻¹ * h.inner (W.embedding x)
          (mfderiv SpatialNeckCylinderModel I W.embedding x v)
          (mfderiv SpatialNeckCylinderModel I W.embedding x v) ∧
      ((spatialNeckScale h p) ^ 2)⁻¹ * h.inner (W.embedding x)
          (mfderiv SpatialNeckCylinderModel I W.embedding x v)
          (mfderiv SpatialNeckCylinderModel I W.embedding x v) ≤
        (13 / 12 : ℝ) ^ 2 * gRef.inner x v v := by
  let gRef := unitCylinderMetric.restrictOpen (spatialNeckBuffer epsilon)
  have href : 0 ≤ gRef.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (gRef.pos x v hv).le
  have hnorm : metricDerivNorm (I := SpatialNeckCylinderModel) 0
      W.normalizedMetric gRef gRef x ≤ 23 / 144 :=
    (W.metricDerivNorm_lt 0 (Nat.zero_le _) x hx).le.trans
      (hsmall.trans spatialNeckControlEpsilon_le)
  have herror := metricDifference_abs_le W.normalizedMetric gRef gRef x v v
  rw [mul_assoc, ← sq, Real.sq_sqrt href] at herror
  have hbound := herror.trans (mul_le_mul_of_nonneg_right hnorm href)
  obtain ⟨hlower, hupper⟩ := abs_le.mp hbound
  rw [W.normalized_inner] at hlower hupper
  change (11 / 12 : ℝ) ^ 2 * gRef.inner x v v ≤ _ ∧
    _ ≤ (13 / 12 : ℝ) ^ 2 * gRef.inner x v v
  constructor <;> nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
