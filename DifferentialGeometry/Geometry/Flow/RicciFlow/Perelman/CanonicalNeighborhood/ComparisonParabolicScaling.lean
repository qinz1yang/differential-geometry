import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Scaling

set_option autoImplicit false
noncomputable section
open Bundle Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]
  {h : ℝ → SmoothRiemannianMetric I N} {g : ℝ → SmoothRiemannianMetric I3 M}
  {F : N → M} {U : Set N} {times : Set ℝ} {order : ℕ} {eps : ℝ}

def MetricComparisonOn.parabolicRescale
    (C : MetricComparisonOn h g F U times order eps)
    (tau c : ℝ) (hc : 0 < c) (p : ℕ) (hp : p ≤ order) (J : Set ℝ) (hJ : UniqueDiffOn ℝ J)
    (hmap : MapsTo (parabolicTime tau c) J times)
    (hdiff : ∀ b s, s ∈ J → ∀ y ∈ U, ∀ v : Fin 2 → TangentSpace I y,
      DifferentiableWithinAt ℝ (fun r => C.jet b r y v) times (parabolicTime tau c s)) :
    MetricComparisonOn (fun s => scaleMetric c hc (h (parabolicTime tau c s)))
      (fun s => scaleMetric c hc (g (parabolicTime tau c s))) F U J p
      ((max 1 (Real.sqrt c)⁻¹) ^ p * eps) where
  pullback s := c • C.pullback (parabolicTime tau c s)
  pullback_eq := by
    intro s y hy v
    simp only [ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply,
      smul_eq_mul, C.pullback_eq _ y hy v, scaleMetric_inner]
  jet b s := (c * c⁻¹ ^ b) • C.jet b (parabolicTime tau c s)
  jet_zero := by
    intro s y v
    simp only [pow_zero, mul_one, ContMDiffSection.coe_smul, Pi.smul_apply,
      Tensor0SSpace.smul_apply, smul_eq_mul, C.jet_zero, scaleMetric_inner, mul_sub]
  jet_succ := by
    intro b s hs y hy v
    have hd : HasDerivWithinAt (fun r => C.jet b r y v)
        (C.jet (b + 1) (parabolicTime tau c s) y v) times (parabolicTime tau c s) := by
      rw [C.jet_succ b _ (hmap hs) y hy v]
      exact (hdiff b s hs y hy v).hasDerivWithinAt
    have ht : HasDerivAt (parabolicTime tau c) c⁻¹ s := by
      have hh := ((hasDerivAt_id s).div_const c).const_add tau
      simp only [one_div] at hh
      exact hh
    have hh := ((hd.scomp s ht.hasDerivWithinAt hmap).const_mul (c * c⁻¹ ^ b)).derivWithin
      (hJ s hs)
    simpa only [ContMDiffSection.coe_smul, Pi.smul_apply, Tensor0SSpace.smul_apply,
      smul_eq_mul, Function.comp_def, pow_succ, mul_assoc] using hh.symm
  equivalence := by
    intro s hs y hy v
    have heps : 0 ≤ eps := (Real.sqrt_nonneg _).trans (C.close 0 0 (by omega) _ (hmap hs) y hy)
    have hle : eps ≤ (max 1 (Real.sqrt c)⁻¹) ^ p * eps := by
      exact le_mul_of_one_le_left heps (one_le_pow₀ (le_max_left _ _))
    have hh := C.equivalence _ (hmap hs) y hy v
    have hlo := mul_le_mul_of_nonneg_left hh.1 hc.le
    have hhi := mul_le_mul_of_nonneg_left hh.2 hc.le
    have hv := inner_self_nonneg (h (parabolicTime tau c s)) y v
    have hloss := mul_nonneg (sub_nonneg.mpr hle) (mul_nonneg hc.le hv)
    simp only [scaleMetric_inner, ContMDiffSection.coe_smul, Pi.smul_apply,
      Tensor0SSpace.smul_apply, smul_eq_mul]
    constructor <;> nlinarith
  close := by
    intro a b hab s hs y hy
    have heps : 0 ≤ eps := (Real.sqrt_nonneg _).trans (C.close 0 0 (by omega) _ (hmap hs) y hy)
    have hcoeff : 0 ≤ c * c⁻¹ ^ b := mul_nonneg hc.le (pow_nonneg (inv_nonneg.mpr hc.le) _)
    have hfactor : (Real.sqrt c)⁻¹ ^ (a + 2) * (c * c⁻¹ ^ b) =
        (Real.sqrt c)⁻¹ ^ (a + 2 * b) := by
      have hinv : c⁻¹ ^ b = (Real.sqrt c)⁻¹ ^ (2 * b) := by
        rw [pow_mul, inv_pow (Real.sqrt c) 2, Real.sq_sqrt hc.le]
      have hcancel : (Real.sqrt c)⁻¹ ^ 2 * c = 1 := by
        rw [inv_pow, Real.sq_sqrt hc.le, inv_mul_cancel₀ hc.ne']
      rw [hinv, pow_add, pow_add]
      calc
        _ = ((Real.sqrt c)⁻¹ ^ 2 * c) *
            ((Real.sqrt c)⁻¹ ^ a * (Real.sqrt c)⁻¹ ^ (2 * b)) := by ring
        _ = _ := by rw [hcancel, one_mul]
    have hweight : (Real.sqrt c)⁻¹ ^ (a + 2 * b) ≤ (max 1 (Real.sqrt c)⁻¹) ^ p :=
      (pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg c)) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) hab)
    rw [tensor02CovDerivNormWith_smul, tensor02CovDerivNormWith_scaleMetric,
      abs_of_nonneg hcoeff]
    calc
      _ = (Real.sqrt c)⁻¹ ^ (a + 2 * b) *
          tensor02CovDerivNormWith a (C.jet b (parabolicTime tau c s))
            (h (parabolicTime tau c s)) (h (parabolicTime tau c s)) y := by
        rw [← mul_assoc, mul_comm (c * c⁻¹ ^ b), hfactor]
      _ ≤ (Real.sqrt c)⁻¹ ^ (a + 2 * b) * eps :=
        mul_le_mul_of_nonneg_left (C.close a b (hab.trans hp) _ (hmap hs) y hy) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hweight heps

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
