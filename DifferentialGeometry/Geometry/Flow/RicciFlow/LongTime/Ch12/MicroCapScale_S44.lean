import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroWholeBallShi_O13

/-!
# CH12-S44, group 1: scale conversion for the recent-cap branch of `hpt` (ZC)

At a recent-cap point `y` the cap-window jets of the W5 kernel are stated at the cap scale `q`
(`|∇^j Rm|² ≤ q^(j+2) B_j`).  Together with a scalar lower bound `q/4 ≤ R(y)` on the flowed cap
core and the zero-order bound `R(y) ≤ C₀ ρ⁻²` (Z0 at the micro ball) this gives the right branch of
`hpt`: `|∇^k Rm|(y) ≤ B k ρ^-(k+2)`.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

/-- The cap scale is controlled by the micro scale: `q/4 ≤ R(y) ≤ C₀ ρ⁻²` ⇒ `q ≤ 4 C₀ ρ⁻²`. -/
theorem capScale_le_of_scalar_S44 {q ρ C₀ R : ℝ} (hlow : q / 4 ≤ R)
    (hZ0 : R ≤ C₀ / ρ ^ 2) : q ≤ 4 * C₀ / ρ ^ 2 := by
  have h : q / 4 ≤ C₀ / ρ ^ 2 := hlow.trans hZ0
  have : q ≤ 4 * (C₀ / ρ ^ 2) := by linarith
  simpa [mul_div_assoc] using this

/-- **Scale conversion (F6).**  Jets of order `k` at cap scale `q` and `q ≤ 4 C₀ ρ⁻²` give the
`ρ`-scale bound `|∇^k Rm| ≤ √B_k (2√C₀)^(k+2) ρ^-(k+2)`. -/
theorem curvatureDerivativeNorm_le_of_capJets_S44 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (y : M) (k : ℕ) (q ρ C₀ Bk : ℝ)
    (hq : 0 < q) (hρ : 0 < ρ) (hC₀ : 0 < C₀) (hB : 0 ≤ Bk)
    (hjet : CheegerGromovCompactness.curvDerivNormSq k g y ≤ q ^ (k + 2) * Bk)
    (hqρ : q ≤ 4 * C₀ / ρ ^ 2) :
    curvatureDerivativeNorm g k y ≤ Real.sqrt Bk * (2 * Real.sqrt C₀) ^ (k + 2) * (ρ ^ (k + 2))⁻¹ := by
  have hX0 : 0 ≤ curvatureDerivativeNorm g k y := curvatureDerivativeNorm_nonneg g k y
  have hsq := curvatureDerivativeNorm_sq_eq_curvDerivNormSq g k y
  set K : ℝ := (2 * Real.sqrt C₀) ^ (k + 2) * (ρ ^ (k + 2))⁻¹ with hK
  have hK0 : 0 ≤ K := by positivity
  have hK2 : K ^ 2 = (4 * C₀ / ρ ^ 2) ^ (k + 2) := by
    have h4 : (2 * Real.sqrt C₀) ^ 2 = 4 * C₀ := by
      rw [mul_pow, Real.sq_sqrt hC₀.le]; ring
    have e1 : ((2 * Real.sqrt C₀) ^ (k + 2)) ^ 2 = (4 * C₀) ^ (k + 2) := by
      rw [← h4, ← pow_mul, ← pow_mul, Nat.mul_comm (k + 2) 2]
    have e2 : ((ρ ^ (k + 2))⁻¹) ^ 2 = ((ρ ^ 2) ^ (k + 2))⁻¹ := by
      rw [inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm (k + 2) 2]
    rw [hK, mul_pow, e1, e2, div_pow, div_eq_mul_inv]
  have hqpow : q ^ (k + 2) ≤ (4 * C₀ / ρ ^ 2) ^ (k + 2) :=
    pow_le_pow_left₀ hq.le hqρ _
  have hX2 : curvatureDerivativeNorm g k y ^ 2 ≤ Bk * K ^ 2 := by
    rw [hsq, hK2]
    calc CheegerGromovCompactness.curvDerivNormSq k g y ≤ q ^ (k + 2) * Bk := hjet
      _ ≤ (4 * C₀ / ρ ^ 2) ^ (k + 2) * Bk := mul_le_mul_of_nonneg_right hqpow hB
      _ = Bk * (4 * C₀ / ρ ^ 2) ^ (k + 2) := mul_comm _ _
  have hrhs : Real.sqrt Bk * (2 * Real.sqrt C₀) ^ (k + 2) * (ρ ^ (k + 2))⁻¹ = Real.sqrt Bk * K := by
    rw [hK]; ring
  rw [hrhs]
  by_contra hcon
  have hcon := lt_of_not_ge hcon
  have h1 : (Real.sqrt Bk * K) ^ 2 < curvatureDerivativeNorm g k y ^ 2 :=
    pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
  have h2 : (Real.sqrt Bk * K) ^ 2 = Bk * K ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hB]
  linarith

/-- **`hpt`, right branch (all orders), from cap-scale jets + scalar lower bound + Z0.**
`B k := √(Bj k) (2√C₀)^(k+2)`. -/
theorem hptRight_of_capJets_S44 {M : Type*} [TopologicalSpace M]
    [ChartedSpace ThreeSpace M] [IsManifold ThreeModel ∞ M] [T2Space M]
    (g : SmoothRiemannianMetric ThreeModel M) (y : M) (q ρ C₀ : ℝ) (Bj : ℕ → ℝ)
    (hq : 0 < q) (hρ : 0 < ρ) (hC₀ : 0 < C₀) (hB : ∀ k, 0 ≤ Bj k)
    (hjets : ∀ k : ℕ, CheegerGromovCompactness.curvDerivNormSq k g y ≤ q ^ (k + 2) * Bj k)
    (hlow : q / 4 ≤ metricScalarAt g y) (hZ0 : metricScalarAt g y ≤ C₀ / ρ ^ 2) :
    ∀ k : ℕ, curvatureDerivativeNorm g k y ≤
      (Real.sqrt (Bj k) * (2 * Real.sqrt C₀) ^ (k + 2)) * (ρ ^ (k + 2))⁻¹ := fun k =>
  curvatureDerivativeNorm_le_of_capJets_S44 g y k q ρ C₀ (Bj k) hq hρ hC₀ (hB k) (hjets k)
    (capScale_le_of_scalar_S44 hlow hZ0)

end GC.LongTime.Ch12
