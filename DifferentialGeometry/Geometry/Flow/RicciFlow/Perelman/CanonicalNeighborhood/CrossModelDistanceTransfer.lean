import DifferentialGeometry.Geometry.Comparison.MetricDistanceTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CrossModelBallCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CollarMetricControl


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open Bundle Set
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

section ThreeDimensional

universe u v

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace ThreeSpace M] [ChartedSpace ThreeSpace N]
  [IsManifold I3 ∞ M] [IsManifold I3 ∞ N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem crossModel_metricDistance_transfer [T2Space M] [T2Space N]
    (h : SmoothRiemannianMetric I3 N) (g : SmoothRiemannianMetric I3 M)
    (F : PartialDiffeomorph I3 I3 N M ∞) (p : N) {R eps rho : ℝ}
    (hR : 0 < R) (heps0 : 0 ≤ eps) (heps1 : eps < 1) (hrho : 0 ≤ rho)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hequiv : ∀ y ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace I3 y,
      (1 - eps) * h.inner y v v ≤
          g.inner (F y) (mfderiv I3 I3 (F : N → M) y v) (mfderiv I3 I3 (F : N → M) y v) ∧
        g.inner (F y) (mfderiv I3 I3 (F : N → M) y v)
            (mfderiv I3 I3 (F : N → M) y v) ≤
          (1 + eps) * h.inner y v v)
    (hroom : Real.sqrt (1 + eps) * (3 * rho) < Real.sqrt (1 - eps) * R) :
    ∀ a ∈ riemannianClosedBallOf h p rho, ∀ b ∈ riemannianClosedBallOf h p rho,
      Real.sqrt (1 - eps) * metricDistance h a b ≤ metricDistance g (F a) (F b) ∧
        metricDistance g (F a) (F b) ≤ Real.sqrt (1 + eps) * metricDistance h a b :=
  crossModel_toReal_transfer h g F p hR heps0 heps1 hrho hcpt hsource hequiv hroom

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem crossModel_edist_transfer_of_comparison [T2Space M] [T2Space N]
    [SigmaCompactSpace N]
    (h : SmoothRiemannianMetric I3 N) (g : SmoothRiemannianMetric I3 M)
    (F : PartialDiffeomorph I3 I3 N M ∞) {U : Set N} {order : ℕ} {eps : ℝ}
    (cmp : MetricComparisonOn (fun _ => h) (fun _ => g) (F : N → M) U {0} order eps)
    (p : N) {R rho : ℝ}
    (hR : 0 < R) (heps0 : 0 ≤ eps) (heps1 : eps < 1) (hrho : 0 ≤ rho)
    (hcpt : IsCompact (riemannianClosedBallOf h p R))
    (hball : riemannianClosedBallOf h p R ⊆ U)
    (hsource : riemannianClosedBallOf h p R ⊆ F.source)
    (hroom : Real.sqrt (1 + eps) * (3 * rho) < Real.sqrt (1 - eps) * R) :
    ∀ a ∈ riemannianClosedBallOf h p rho, ∀ b ∈ riemannianClosedBallOf h p rho,
      ENNReal.ofReal (Real.sqrt (1 - eps)) * riemannianEDistOf (I := I3) h a b ≤
          riemannianEDistOf (I := I3) g (F a) (F b) ∧
        riemannianEDistOf (I := I3) g (F a) (F b) ≤
          ENNReal.ofReal (Real.sqrt (1 + eps)) * riemannianEDistOf (I := I3) h a b := by
  have hequiv : ∀ y ∈ riemannianClosedBallOf h p R, ∀ v : TangentSpace I3 y,
      (1 - eps) * h.inner y v v ≤
          g.inner (F y) (mfderiv I3 I3 (F : N → M) y v)
            (mfderiv I3 I3 (F : N → M) y v) ∧
        g.inner (F y) (mfderiv I3 I3 (F : N → M) y v)
            (mfderiv I3 I3 (F : N → M) y v) ≤
          (1 + eps) * h.inner y v v := by
    intro y hy v
    have hyU : y ∈ U := hball hy
    have heq := cmp.pullback_eq 0 y hyU (fun _ => v)
    have hcmp := cmp.equivalence 0 rfl y hyU v
    refine ⟨?_, ?_⟩
    · have h1 := hcmp.1
      rwa [heq] at h1
    · have h2 := hcmp.2
      rwa [heq] at h2
  exact crossModel_edist_transfer h g F p hR heps0 heps1 hrho hcpt hsource hequiv hroom

end ThreeDimensional


theorem crossModel_room_of_length_scale_bound {eps Lplus : ℝ}
    (heps0 : 0 < eps) (hL : 0 ≤ Lplus)
    (hbig : 10 * Lplus + 10 < Real.sqrt eps⁻¹) :
    Real.sqrt (1 + eps) * (3 * (3 * Lplus / Real.sqrt (1 - eps))) <
      Real.sqrt (1 - eps) * Real.sqrt eps⁻¹ := by
  have hS2 : Real.sqrt eps⁻¹ ^ 2 = eps⁻¹ := Real.sq_sqrt (by positivity)
  have hS10 : (10 : ℝ) ≤ Real.sqrt eps⁻¹ := by linarith
  have hinv : (100 : ℝ) ≤ eps⁻¹ := by nlinarith
  have hepssmall : eps ≤ 1 / 100 := by
    have hmul : eps * eps⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt heps0)
    nlinarith
  have h1e : (0 : ℝ) < 1 - eps := by linarith
  have hLm : (0 : ℝ) < Real.sqrt (1 - eps) := Real.sqrt_pos.mpr h1e
  have hLpub : Real.sqrt (1 + eps) ≤ 1 + eps := by
    have hstep := Real.sqrt_le_sqrt (show (1 : ℝ) + eps ≤ (1 + eps) ^ 2 by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at hstep
  have hLHS : Real.sqrt (1 + eps) * (3 * (3 * Lplus / Real.sqrt (1 - eps))) =
      (Real.sqrt (1 + eps) * (9 * Lplus)) / Real.sqrt (1 - eps) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  have hRHS : Real.sqrt (1 - eps) * Real.sqrt eps⁻¹ * Real.sqrt (1 - eps) =
      Real.sqrt eps⁻¹ * (1 - eps) := by
    rw [show Real.sqrt (1 - eps) * Real.sqrt eps⁻¹ * Real.sqrt (1 - eps) =
        Real.sqrt eps⁻¹ * (Real.sqrt (1 - eps) * Real.sqrt (1 - eps)) from by ring,
      Real.mul_self_sqrt h1e.le]
  have hA : Real.sqrt (1 + eps) * (9 * Lplus) ≤ 101 / 100 * (9 * Lplus) :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have hB1 : (10 * Lplus + 10) * (1 - eps) ≤ Real.sqrt eps⁻¹ * (1 - eps) :=
    mul_le_mul_of_nonneg_right hbig.le h1e.le
  have hB2 : (10 * Lplus + 10) * (99 / 100) ≤ (10 * Lplus + 10) * (1 - eps) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  rw [hLHS, div_lt_iff₀ hLm, hRHS]
  nlinarith [hA, hB1, hB2, hL]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
