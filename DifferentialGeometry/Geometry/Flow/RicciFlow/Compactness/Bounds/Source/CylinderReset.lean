import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Bounds.Source.BackwardCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Shi.Derivatives.LocalCompact
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ShrinkingCylinder
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NormalizedConvergence
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.ScalarConvergence
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Norm.ReferenceChange

set_option autoImplicit false
noncomputable section
open Set Filter Bundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private local instance : Fact (Module.finrank ℝ ThreeSpace = 2 + 1) := ⟨by simp⟩

theorem exists_curvature_derivative_bounds_before_time_of_cylinder_convergence
    {δ b : ℝ} (hδ : 0 < δ) (hb : b ≤ 0) {D : RealTimeInterval}
    (S : ℕ → SolutionOn (I := NeckCylinderModel) (M := neckBuffer δ) D)
    (hS : ∀ n, IsSolutionOn (S n)) (C : ℝ≥0)
    (hslab : Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b ⊆ D.carrier)
    (hreg : Ioo (b - (12 * ((C : ℝ) + 1))⁻¹) b ⊆ D.regular)
    (hconv : ∀ K : Set (neckBuffer δ), IsCompact K → MetricCPConvergenceOn K 2
      (fun n => (S n).base.metric b)
      ((PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) b).restrictOpen (neckBuffer δ))
      (roundCylinderMetric.restrictOpen (neckBuffer δ)))
    (q Q : ℕ → ℝ) (hq : ∀ᶠ n in atTop, q n ≤ 1) (hQ : Tendsto Q atTop atTop)
    (hderiv : ∀ K : Set (neckBuffer δ), IsCompact K → ∀ᶠ n in atTop,
      ∀ x ∈ K, ∀ t ∈ Ioo (b - (12 * ((C : ℝ) + 1))⁻¹) b,
        q n < (S n).scalar t x →
        |derivWithin (fun s => (S n).scalar s x) (Iic t) t| ≤ C * (S n).scalar t x ^ 2)
    {Phi : ℝ → ℝ} (hPhi : AdmissiblePinchingFunction Phi)
    (hpinch : ∀ᶠ n in atTop, PhiAlmostNonnegative (S n)
      (Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b) (rescalePinchingFunction (Q n) Phi)) :
    (∀ K : Set (neckBuffer δ), IsCompact K → ∀ᶠ n in atTop,
      ∀ t ∈ Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b, ∀ x ∈ K,
        curvDerivNormSq 0 ((S n).base.metric t) x ≤ (12 * Real.sqrt 3) ^ 2) ∧
    ∀ K : Set (neckBuffer δ), IsCompact K → ∃ B : ℕ → ℝ, (∀ m, 0 ≤ B m) ∧
      ∀ᶠ n in atTop, ∀ m : ℕ, ∀ t ∈ Icc (b - (12 * ((C : ℝ) + 1))⁻¹ / 2) b,
        ∀ x ∈ K, curvDerivNorm m ((S n).base.metric t) x ≤ B m := by
  let _ : SigmaCompactSpace (neckBuffer δ) := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen NeckCylinderModel (neckBuffer δ).isOpen)
  let R := (PDE.RicciFlow.shrinkingCylinderMetric (E := ThreeSpace) b).restrictOpen (neckBuffer δ)
  let p : neckBuffer δ := ⟨(Geometry.Neck.spherePoint, 0), by
    have := inv_pos.mpr hδ
    constructor <;> linarith⟩
  let F : ℕ → PointedFlowData NeckCylinderModel D := fun n => {
    M := neckBuffer δ
    topology := inferInstance
    charted := inferInstance
    smooth := inferInstance
    sigmaCompact := inferInstance
    t2 := inferInstance
    t2TangentBundle := inferInstance
    basepoint := p
    S := S n
    isSolution := hS n }
  have hzero : ∀ K : Set (neckBuffer δ), IsCompact K → ∀ᶠ n in atTop,
      ∀ t ∈ Icc (b - (12 * ((C : ℝ) + 1))⁻¹) b, ∀ x ∈ K,
        curvDerivNormSq 0 ((S n).base.metric t) x ≤ (12 * Real.sqrt 3) ^ 2 := by
    intro K hK
    have hscalarConv : TendstoUniformlyOn (fun n x => (F n).S.scalar b x)
        (fun _ => (1 - b)⁻¹) atTop K := by
      have hc := (hconv K hK).tendstoUniformlyOn_metricScalarAt hK
      have hmodel : (fun x : neckBuffer δ => metricScalarAt R x) = fun _ => (1-b)⁻¹ := by
        funext x
        rw [metricScalarAt_restrictOpen, PDE.RicciFlow.shrinkingCylinderMetric_scalar (hb.trans_lt zero_lt_one)]
      rw [hmodel] at hc
      exact hc
    have hbound := (eventually_riemannNorm_le_on_backward_interval_of_rescaling_tendsto_atTop
      F (fun _ => id) (C := C) (inv_le_one_of_one_le₀ (by linarith : 1 ≤ 1 - b))
      (by simp [Module.finrank_prod]) hslab hscalarConv hq (hderiv K hK) hPhi hQ hpinch).2
    filter_upwards [hbound] with n hn t ht x hx
    have hb := hn x hx t ht
    have hnonneg : 0 ≤ curvDerivNormSq 0 ((S n).base.metric t) x :=
      normSq0S_nonneg _ _ _ _
    have hs := Real.sq_sqrt hnonneg
    change Real.sqrt (curvDerivNormSq 0 ((S n).base.metric t) x) ≤ 12 * Real.sqrt 3 at hb
    nlinarith [Real.sqrt_nonneg (curvDerivNormSq 0 ((S n).base.metric t) x)]
  refine ⟨hzero, ?_⟩
  intro K hK
  have ha : b - (12 * ((C : ℝ) + 1))⁻¹ < b :=
    sub_lt_self _ (by positivity)
  have hterminal : ∀ A : Set (neckBuffer δ), IsCompact A → MetricCPConvergenceOn A 0
      (fun n => (S n).base.metric b) R R := by
    intro A hA ε hε
    obtain ⟨L, hL, hnorm⟩ := exists_metric_deriv_norm_reference_bound hA
      (roundCylinderMetric.restrictOpen (neckBuffer δ)) R 0
    let η := ε / (2 * (L + 1))
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨j, hj⟩ := hconv A hA η hη
    refine ⟨j, fun n hn => ?_⟩
    apply lt_of_le_of_lt (metricDerivNormSupOn_le_of_forall A 0 _ _ _
      (ε / 2) (by positivity) ?_) (by linarith)
    intro m hm x hx
    have hm0 : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    have hsource : metricDerivNorm 0 ((S n).base.metric b) R
        (roundCylinderMetric.restrictOpen (neckBuffer δ)) x ≤ η :=
      (derivNorm_le_sup hA (by omega : 0 ≤ 2) _ _ _ hx).trans (hj n hn).le
    have htarget := hnorm ((S n).base.metric b) R 0 le_rfl x hx
    simp only [Nat.zero_add, Finset.sum_range_one] at htarget
    have hscaled : L * η ≤ ε / 2 := by
      have hcancel : (L + 1) * η = ε / 2 := by
        dsimp only [η]
        field_simp
      rw [← hcancel]
      exact mul_le_mul_of_nonneg_right (by linarith) hη.le
    exact htarget.trans ((mul_le_mul_of_nonneg_left hsource hL).trans hscaled)
  have hc := exists_eventually_curvDerivNorm_on_compact_of_terminal_convergence S hS R ha
    hslab hreg hterminal
    (fun A hA => ⟨(12 * Real.sqrt 3) ^ 2, hzero A hA⟩) K hK
  have heq : (b - (12 * ((C : ℝ) + 1))⁻¹ + b) / 2 =
      b - (12 * ((C : ℝ) + 1))⁻¹ / 2 := by ring
  rwa [heq] at hc

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
