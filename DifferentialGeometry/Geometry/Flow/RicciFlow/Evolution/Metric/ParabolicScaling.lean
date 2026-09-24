import DifferentialGeometry.Geometry.Metric.Variation.TimeDerivative
import DifferentialGeometry.Geometry.Connection.LeviCivita.Scaling
import Mathlib.Analysis.Calculus.Deriv.Mul


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [BoundarylessManifold I M]


theorem ricciSharp_scaleMetric (Q : ℝ) (hQ : 0 < Q)
    (g : SmoothRiemannianMetric I M) (x : M) :
    ricciSharp (scaleMetric Q hQ g) x = Q⁻¹ • ricciSharp g x := by
  have hRic (v w : TangentSpace I x) :
      ricciTensor (scaleMetric Q hQ g) x v w = ricciTensor g x v w := by
    rw [ricciTensor_apply, ricciTensor_apply]
    congr 1
    ext z
    simp only [ricciEndo_apply, LeviCivita, lcConn_scaleMetric]
  ext v
  change ricciSharpVec (scaleMetric Q hQ g) x v = Q⁻¹ • ricciSharp g x v
  symm
  apply ricciSharpVec_unique
  intro w
  rw [scaleMetric_inner, map_smul, smul_apply,
    smul_eq_mul, inner_ricciSharp, hRic, ← mul_assoc, mul_inv_cancel₀ hQ.ne', one_mul]

omit [FiniteDimensional ℝ E] [T2Space M] [BoundarylessManifold I M] in
theorem covariantEndomorphismAction0S_smul_smul {r : ℕ} {x : M}
    (A : Tensor0SSpace r I x) (L : TangentSpace I x →L[ℝ] TangentSpace I x)
    (c d : ℝ) :
    covariantEndomorphismAction0S (c • A) (d • L) =
      (c * d) • covariantEndomorphismAction0S A L := by
  apply tensor0SSpace_ext
  intro v
  simp only [covariantEndomorphismAction0S_apply, smul_apply,
    Tensor0SSpace.map_update_smul, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => (mul_assoc _ _ _).symm


theorem metricTimeDerivWithin_parabolic_of_mapsTo
    (g : ℝ → SmoothRiemannianMetric I M) {r : ℕ} {x : M}
    (A : ℝ → Tensor0SSpace r I x) {J K : Set ℝ} {t₀ Q s : ℝ}
    (hQ : 0 < Q) (c : ℝ)
    (hmaps : MapsTo (fun u : ℝ => t₀ + u / Q) K J)
    (hK : UniqueDiffWithinAt ℝ K s)
    (hA : DifferentiableWithinAt ℝ A J (t₀ + s / Q)) :
    metricTimeDerivWithin (fun u => scaleMetric Q hQ (g (t₀ + u / Q)))
        K (fun u => c • A (t₀ + u / Q)) s =
      (c * Q⁻¹) • metricTimeDerivWithin g J A (t₀ + s / Q) := by
  have htime : HasDerivAt (fun u : ℝ => t₀ + u / Q) Q⁻¹ s := by
    convert ((hasDerivAt_id s).div_const Q).const_add t₀ using 1 <;>
      first | rfl | simp only [one_div]
  have hd : HasDerivWithinAt (fun u => c • A (t₀ + u / Q))
      (c • (Q⁻¹ • derivWithin A J (t₀ + s / Q))) K s :=
    (hA.hasDerivWithinAt.scomp s htime.hasDerivWithinAt hmaps).const_smul c
  have hd' : derivWithin (fun u => c • A (t₀ + u / Q)) K s =
      (c * Q⁻¹) • derivWithin A J (t₀ + s / Q) := by
    have heq := hd.derivWithin hK
    rw [smul_smul] at heq
    exact heq
  rw [metricTimeDerivWithin, hd', ricciSharp_scaleMetric,
    covariantEndomorphismAction0S_smul_smul, ← smul_add]
  rfl

theorem metricTimeDerivWithin_parabolic
    (g : ℝ → SmoothRiemannianMetric I M) {r : ℕ} {x : M}
    (A : ℝ → Tensor0SSpace r I x) {b t₀ Q s : ℝ}
    (hQ : 0 < Q) (ht₀ : t₀ ≤ b) (hs : s ≤ 0) (c : ℝ)
    (hA : DifferentiableWithinAt ℝ A (Iic b) (t₀ + s / Q)) :
    metricTimeDerivWithin (fun u => scaleMetric Q hQ (g (t₀ + u / Q)))
        (Iic 0) (fun u => c • A (t₀ + u / Q)) s =
      (c * Q⁻¹) • metricTimeDerivWithin g (Iic b) A (t₀ + s / Q) := by
  apply metricTimeDerivWithin_parabolic_of_mapsTo g A hQ c _
    (uniqueDiffOn_Iic 0 s hs) hA
  intro u hu
  exact (add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hu hQ.le)).trans ht₀

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
