import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.WeylSummability
import DifferentialGeometry.Analysis.Parabolic.MaximalRegularity.Synthesis
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Time-continuity of spectral series in the tensor Sobolev scale

A Weierstrass `M`-test for `tensorHs g 0 2 σ`-valued families that are presented through
their eigenbasis coordinates.  If a family `W : ℝ → tensorHs g 0 2 σ` has coordinates
`(W t).coeff i = φ i t` with each `φ i` continuous on a set `s`, and a single uniform-in-`t`
summable majorant on the **higher**-order weighted coordinate squares
`tensorSobolevWeight i σ' · (φ i t)² ≤ Cmaj i` with `σ' - σ` above the Weyl summability
threshold, then `W` is continuous on `s` in the order-`σ` Sobolev norm.

The eigenbasis expansion `W t = ∑ᵢ (φ i t) • bᵢ` (`tensorHs.hasSum_smul_basisVec`) presents
`W` as a series of continuous functions; the per-mode norm is
`‖(φ i t) • bᵢ‖ = |φ i t| · √(tensorSobolevWeight i σ)`, whose square at order `σ` is bounded,
*uniformly in `t`*, by the geometric-mean / arithmetic-mean split

  `tensorSobolevWeight i σ · (φ i t)² = tensorSobolevWeight i (-(σ' - σ)) ·
      (tensorSobolevWeight i σ' · (φ i t)²)
    ≤ tensorSobolevWeight i (-(σ' - σ)) · Cmaj i`,

and `‖(φ i t) • bᵢ‖ ≤ ½ (tensorSobolevWeight i (-(σ' - σ)) + Cmaj i)` by `2ab ≤ a² + b²`.
The right side is summable: the negative-weight tail is `tensorEigen_summable_negpow` (Weyl)
and `Cmaj` is summable by hypothesis.  Mathlib's `continuousOn_tsum` then delivers the
continuity of the limit `t ↦ ∑ᵢ (φ i t) • bᵢ = W t`.

This is the analytic engine behind the order-`(a+2)` time-continuity of the realized
Ricci–DeTurck solution field. -/

namespace DifferentialGeometry

open Bundle Manifold MeasureTheory Set Filter
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace Analysis
namespace Parabolic
namespace TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- **Weierstrass `M`-test for an eigen-coordinate-presented family in `Hˢ`.**

For a family `W : ℝ → tensorHs g 0 2 σ` whose eigenbasis coordinates are `(W t).coeff i =
φ i t` on a set `s`, with each coordinate function `φ i` continuous on `s` and a single
uniform-in-`t` summable majorant on the *higher*-order weighted coordinate squares —
`tensorSobolevWeight i σ' · (φ i t)² ≤ Cmaj i` for all `i` and `t ∈ s`, with `Summable Cmaj`
and `σ' - σ` strictly above the Weyl exponent `weylSobolevExp` — the family `W` is continuous
on `s` in the order-`σ` Sobolev norm. -/
theorem tensorHs_continuousOn_of_coeff_of_higher_mass
    (g : SmoothRiemannianMetric I M) {σ σ' : ℝ}
    (hσσ' : ((weylSobolevExp (E := E) : ℕ) : ℝ) < σ' - σ)
    {s : Set ℝ} (W : ℝ → tensorHs (I := I) (M := M) g 0 2 σ)
    (φ : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → ℝ)
    (hcoeff : ∀ t ∈ s, ∀ i, (W t).coeff i = φ i t)
    (hφ_cont : ∀ i, ContinuousOn (φ i) s)
    {Cmaj : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ} (hCmaj : Summable Cmaj)
    (hmass : ∀ i, ∀ t ∈ s,
      tensorSobolevWeight (I := I) (M := M) i σ' * (φ i t) ^ 2 ≤ Cmaj i) :
    ContinuousOn W s := by
  classical

  set negWeight : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => tensorSobolevWeight (I := I) (M := M) i (-(σ' - σ)) with hnegWeight
  have hnegWeight_sum : Summable negWeight :=
    tensorEigen_summable_negpow (I := I) (M := M) g (σ' - σ) hσσ'
  set U : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ :=
    fun i => (negWeight i + Cmaj i) / 2 with hU
  have hU_sum : Summable U :=
    ((hnegWeight_sum.add hCmaj).div_const 2)

  set f : TensorEigenIdx (I := I) (M := M) g 0 2 → ℝ → tensorHs (I := I) (M := M) g 0 2 σ :=
    fun i t => φ i t •
      tensorHsBasisVec (I := I) (M := M) (g := g) (r := 0) (s := 2) σ i with hf

  have hf_cont : ∀ i, ContinuousOn (f i) s := by
    intro i
    exact (hφ_cont i).smul continuousOn_const

  have hf_bound : ∀ i, ∀ t ∈ s, ‖f i t‖ ≤ U i := by
    intro i t ht
    have hnorm : ‖f i t‖ =
        |φ i t| * Real.sqrt (tensorSobolevWeight (I := I) (M := M) i σ) := by
      rw [hf, norm_smul, Real.norm_eq_abs, norm_tensorHsBasisVec]

    have hsq : ‖f i t‖ ^ 2 = tensorSobolevWeight (I := I) (M := M) i σ * (φ i t) ^ 2 := by
      rw [hnorm, mul_pow, sq_abs, sq_sqrt_tensorSobolevWeight]
      ring

    have hsplit : tensorSobolevWeight (I := I) (M := M) i σ =
        negWeight i * tensorSobolevWeight (I := I) (M := M) i σ' := by
      have hbase : (0 : ℝ) < 1 + TensorEigenIdx.lambda (I := I) (M := M) i :=
        lt_of_lt_of_le one_pos (one_le_one_add_lambda (I := I) (M := M) i)
      rw [hnegWeight]
      unfold tensorSobolevWeight
      rw [← Real.rpow_add hbase, show -(σ' - σ) + σ' = σ from by ring]

    have hsq_le : ‖f i t‖ ^ 2 ≤ negWeight i * Cmaj i := by
      rw [hsq, hsplit, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hmass i t ht)
        (by rw [hnegWeight]; exact tensorSobolevWeight_nonneg (I := I) (M := M) i _)

    have hnW_nonneg : 0 ≤ negWeight i := by
      rw [hnegWeight]; exact tensorSobolevWeight_nonneg (I := I) (M := M) i _
    have hC_nonneg : 0 ≤ Cmaj i :=
      le_trans (mul_nonneg (tensorSobolevWeight_nonneg (I := I) (M := M) i σ') (sq_nonneg _))
        (hmass i t ht)
    have hnorm_nonneg : 0 ≤ ‖f i t‖ := norm_nonneg _
    have hsqrt : ‖f i t‖ ≤ Real.sqrt (negWeight i * Cmaj i) := by
      rw [show ‖f i t‖ = Real.sqrt (‖f i t‖ ^ 2) from (Real.sqrt_sq hnorm_nonneg).symm]
      exact Real.sqrt_le_sqrt hsq_le
    have hgeom : Real.sqrt (negWeight i * Cmaj i) ≤ U i := by
      rw [hU, Real.sqrt_mul hnW_nonneg]
      have h2 : 2 * Real.sqrt (negWeight i) * Real.sqrt (Cmaj i) ≤
          Real.sqrt (negWeight i) ^ 2 + Real.sqrt (Cmaj i) ^ 2 :=
        two_mul_le_add_sq _ _
      rw [Real.sq_sqrt hnW_nonneg, Real.sq_sqrt hC_nonneg] at h2
      linarith
    exact hsqrt.trans hgeom

  have hcont_tsum : ContinuousOn (fun t => ∑' i, f i t) s :=
    continuousOn_tsum hf_cont hU_sum (fun i t ht => hf_bound i t ht)

  refine hcont_tsum.congr ?_
  intro t ht
  have hsum : HasSum
      (fun i => (W t).coeff i •
        tensorHsBasisVec (I := I) (M := M) (g := g) (r := 0) (s := 2) σ i) (W t) :=
    tensorHs.hasSum_smul_basisVec (W t)
  have hsum' : HasSum (fun i => f i t) (W t) := by
    refine hsum.congr_fun ?_
    intro i
    rw [hf, hcoeff t ht i]
  exact (hsum'.tsum_eq).symm

end TensorHeatEquation
end Parabolic
end Analysis
end DifferentialGeometry
