import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.ParabolicScaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.RegularizedEquality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength.Defs
import Mathlib.Data.Real.Pointwise

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem lRegularizedCostC1_parabolic
    (S : SolutionOn (I := I) (M := M) D)
    (t0 R T a b : ℝ) (hR : 0 < R) (ht0 : t0 ∈ D.carrier) (x y : M) :
    lRegularizedCostC1 (parabolicSolution S t0 R hR ht0) (parabolicBackward t0 R T)
        (Real.sqrt R * a) (Real.sqrt R * b) x y =
      Real.sqrt R * lRegularizedCostC1 S T a b x y := by
  have hsqrt : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
  unfold lRegularizedCostC1
  conv_rhs => rw [← smul_eq_mul]
  rw [← Real.sInf_smul_of_nonneg (Real.sqrt_nonneg R)]
  congr 1
  ext z
  constructor
  · rintro ⟨beta, hbeta, hba, hbb, hbaction⟩
    let alpha : ℝ → M := fun r => beta (Real.sqrt R * r)
    have halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha :=
      hbeta.comp (contMDiff_const.mul contMDiff_id)
    refine Set.mem_smul_set.mpr ⟨lRegularizedAction S T alpha a b,
      ⟨alpha, halpha, hba, hbb, rfl⟩, ?_⟩
    have heq : (fun r => alpha ((Real.sqrt R)⁻¹ * r)) = beta := by
      funext r
      simp only [alpha, mul_inv_cancel_left₀ hsqrt]
    have hact := lRegularizedAction_parabolic S t0 R T a b hR ht0 alpha
    rw [heq] at hact
    exact hact.symm.trans hbaction
  · rintro ⟨w, ⟨alpha, halpha, ha, hb, haction⟩, hz⟩
    refine ⟨fun r => alpha ((Real.sqrt R)⁻¹ * r),
      halpha.comp (contMDiff_const.mul contMDiff_id), ?_, ?_, ?_⟩
    · simpa only [inv_mul_cancel_left₀ hsqrt] using ha
    · simpa only [inv_mul_cancel_left₀ hsqrt] using hb
    · rw [lRegularizedAction_parabolic S t0 R T a b hR ht0 alpha,
        haction]
      exact hz

theorem lCost_parabolic
    (S : SolutionOn (I := I) (M := M) D)
    (t0 R T tau : ℝ) (hR : 0 < R) (ht0 : t0 ∈ D.carrier)
    (htau : 0 ≤ tau) (x y : M) :
    lCost (parabolicSolution S t0 R hR ht0) (parabolicBackward t0 R T) x y (R * tau) =
      Real.sqrt R * lCost S T x y tau := by
  rw [lCost_eq_lRegularizedCostC1 _ _ _ _ _ (mul_nonneg hR.le htau),
    lCost_eq_lRegularizedCostC1 S T x y tau htau, Real.sqrt_mul hR.le]
  simpa only [mul_zero] using
    lRegularizedCostC1_parabolic S t0 R T 0 (Real.sqrt tau) hR ht0 x y

theorem redLength_parabolic
    (S : SolutionOn (I := I) (M := M) D)
    (t0 R T tau : ℝ) (hR : 0 < R) (ht0 : t0 ∈ D.carrier)
    (htau : 0 ≤ tau) (x y : M) :
    redLength (parabolicSolution S t0 R hR ht0) (parabolicBackward t0 R T) x y (R * tau) =
      redLength S T x y tau := by
  unfold redLength
  rw [lCost_parabolic S t0 R T tau hR ht0 htau x y, Real.sqrt_mul hR.le]
  have hsqrt : Real.sqrt R ≠ 0 := (Real.sqrt_pos.mpr hR).ne'
  rw [show 2 * (Real.sqrt R * Real.sqrt tau) =
    Real.sqrt R * (2 * Real.sqrt tau) by ring]
  exact mul_div_mul_left _ _ hsqrt

end DifferentialGeometry.PDE.RicciFlow.Perelman
