import DifferentialGeometry.PDE.RicciFlow.IntrinsicSpectral.MetricRealization.SpectralWeylCounting
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.EigenvectorSmoothToL2
import DifferentialGeometry.Integral.Measure.Invariance

/-!
# The reproducing-kernel integration step of the spectral Weyl-counting reduction

For a closed (compact, boundaryless) smooth Riemannian manifold `(M, g)` modelled
on a finite-dimensional real inner-product space `E` and ranks `(r, s)`, this file
performs the purely measure-theoretic / spectral **integration step** of the
local-Weyl reproducing-kernel route to the polynomial eigenvalue-counting bound
`EigenvalueCountingBound g r s` (defined in `SpectralWeylCounting.lean`).

## The reproducing-kernel diagonal and its integral

The `L²`-orthonormal tensor eigenbasis `{bᵢ}` of the connection (rough) Laplacian
resolvent has, for each index `i`, a genuine `C^∞` representative
`eigenvectorSmooth g r s i : SmoothCcTensor g r s` whose `L²`-class
is `bᵢ`. The **on-diagonal reproducing kernel** at a point `x : M` over a finite
index set `F` is the pointwise sum of squared Riemannian fibre norms
```
  K_F(x) = ∑_{i ∈ F} ‖bᵢ(x)‖²_g
         = ∑_{i ∈ F} tensorInnerPointwise g r s x (bᵢ(x)) (bᵢ(x)).
```

Two facts are isolated and proved here, **unconditionally**:

* `eigenvectorSmooth_integral_normSq_eq_one` — each eigenvector representative has
  unit `L²` energy: `∫_M ‖bᵢ(x)‖²_g dμ_g = 1`. This is the orthonormality
  `‖bᵢ‖_{L²} = 1` reflected through the `SmoothCcTensor` `L²` norm identity
  `‖S‖² = ∫_M ‖S(x)‖²_g dμ_g`.

* `finsetCard_eq_integral_diagonalKernel` — the cardinality of any finite index set
  `F` equals the integral of its diagonal reproducing kernel:
  `(F.card : ℝ) = ∫_M K_F(x) dμ_g`. This combines the unit-energy identity with the
  finite-sum / Bochner-integral interchange.

The headline reduction is then:

* `eigenvalueCountingBound_of_pointwiseDiagonalKernelBound` — given a polynomial
  pointwise bound on the diagonal reproducing kernel over a threshold-capturing
  family of finsets, `EigenvalueCountingBound g r s` follows by integrating the
  kernel bound against the (finite) Riemannian volume:
  `(count Λ).card = ∫_M K_{count Λ}(x) dμ_g ≤ ∫_M B·Λ^q dμ_g = (B·vol(M))·Λ^q`.

The geometric *content* — the pointwise diagonal bound
`K_F(x) ≲ Λ^q` itself (the local-Weyl reproducing-kernel estimate, obtained from a
supercritical Sobolev embedding applied to the finite eigen-span) — is **not**
proved here; it is the genuine remaining input, isolated as the hypothesis of the
reduction. This file discharges everything *downstream* of that single geometric
estimate: the unit-energy identity, the kernel-integral identity, finiteness of
the relevant integrals, and the volume normalisation.

## Sign convention

Geometer convention `Δ_∇ = -∇*∇`, spectrum `⊆ (-∞, 0]`; resolvent `(1 - Δ_∇)⁻¹`,
eigenvalues `λᵢ ≥ 0`.
-/

noncomputable section

set_option linter.style.setOption false
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace PDE
namespace RicciFlow
namespace IntrinsicSpectral
namespace MetricRealization

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

/-- The squared `SmoothCcTensor` `L²` norm equals the Bochner integral of the
diagonal pointwise tensor pairing of the underlying map. -/
theorem smoothCcTensor_normSq_eq_integral
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (S : SmoothCcTensor g r s) :
    ‖S‖ ^ 2 =
      ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (S.toFun x) (S.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  rw [SmoothCcTensor.norm_def, tensorL2Norm_def,
    Real.sq_sqrt (tensorL2Inner_nonneg (I := I) (M := M) g r s S.toFun)]
  rfl

/-- The `SmoothCcTensor` `L²` norm of an eigenvector smooth representative is `1`:
its `L²`-class is the orthonormal eigenbasis vector `bᵢ`, and the inclusion of
smooth sections into `L²` is norm-preserving on representatives. -/
theorem eigenvectorSmooth_norm_eq_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    ‖eigenvectorSmooth (I := I) (M := M) g r s i‖ = 1 := by
  have h_class : (eigenvectorSmooth (I := I) (M := M) g r s i :
        TensorL2 r s g) =
      tensorResolventEigenbasisVec (I := I) (M := M)
        (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s) i :=
    eigenvectorSmooth_toL2 (I := I) (M := M) g r s i
  have h_one := (tensorResolventEigenbasisVec_orthonormal (I := I) (M := M)
    (g := g) (r := r) (s := s)
    (tensorResolventL2_isCompactOperator (I := I) (M := M) g r s)).norm_eq_one i
  have h_coe : ‖(eigenvectorSmooth (I := I) (M := M) g r s i :
        TensorL2 r s g)‖ =
      ‖eigenvectorSmooth (I := I) (M := M) g r s i‖ :=
    UniformSpace.Completion.norm_coe _
  rw [h_class, h_one] at h_coe
  exact h_coe.symm

/-- **Unit `L²` energy of an eigenvector representative.** The integral over `M`
of the squared Riemannian fibre norm of the smooth representative of the
eigenbasis vector `bᵢ` is `1`. -/
theorem eigenvectorSmooth_integral_normSq_eq_one
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x
        ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x)
        ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x)
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 1 := by
  have h := smoothCcTensor_normSq_eq_integral (I := I) (M := M) g r s
    (eigenvectorSmooth (I := I) (M := M) g r s i)
  rw [eigenvectorSmooth_norm_eq_one (I := I) (M := M) g r s i] at h
  rw [← h]; norm_num

/-- The **on-diagonal reproducing kernel** of the eigenbasis over a finite index
set `F`, at a point `x : M`: the sum over `i ∈ F` of the squared Riemannian fibre
norm of the eigenvector representative `bᵢ` at `x`, expressed via the pointwise
tensor pairing `tensorInnerPointwise g r s x (bᵢ(x)) (bᵢ(x))`. -/
def diagonalKernel (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)) (x : M) : ℝ :=
  ∑ i ∈ F,
    tensorInnerPointwise (I := I) (M := M) g r s x
      ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x)
      ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x)

/-- Each summand of the diagonal kernel is integrable: it is the diagonal pairing
of a smooth compactly-supported eigenvector representative, hence in `L²`. -/
private lemma diagonalKernel_summand_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s) :
    Integrable
      (fun x => tensorInnerPointwise (I := I) (M := M) g r s x
        ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x)
        ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x))
      (riemannianVolumeMeasure (I := I) (M := M) g) :=
  (SmoothCcTensor.memL2_toFun (I := I) (M := M)
    (eigenvectorSmooth (I := I) (M := M) g r s i)).integrable_inner_self

/-- **Cardinality as the integral of the diagonal kernel.** For any finite index
set `F`, the cardinality of `F` equals the Bochner integral over `M` of the
diagonal reproducing kernel `diagonalKernel g r s F`. This is the unit-energy
identity `∫ ‖bᵢ‖²_g = 1` summed over `F`, with the finite-sum / integral
interchange. -/
theorem finsetCard_eq_integral_diagonalKernel
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)) :
    (F.card : ℝ) =
      ∫ x, diagonalKernel (I := I) (M := M) g r s F x
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) := by
  simp only [diagonalKernel]
  rw [MeasureTheory.integral_finset_sum F
    (fun i _ => diagonalKernel_summand_integrable (I := I) (M := M) g r s i)]
  rw [Finset.sum_congr rfl
    (fun i _ => eigenvectorSmooth_integral_normSq_eq_one (I := I) (M := M) g r s i)]
  simp

/-- The diagonal reproducing kernel over a finite index set is integrable: it is a
finite sum of integrable diagonal pairings. -/
private lemma diagonalKernel_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (F : Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s)) :
    Integrable (diagonalKernel (I := I) (M := M) g r s F)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  have h : diagonalKernel (I := I) (M := M) g r s F =
      fun x => ∑ i ∈ F,
        tensorInnerPointwise (I := I) (M := M) g r s x
          ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x)
          ((eigenvectorSmooth (I := I) (M := M) g r s i).toFun x) := rfl
  rw [h]
  exact MeasureTheory.integrable_finset_sum F
    (fun i _ => diagonalKernel_summand_integrable (I := I) (M := M) g r s i)

/-- **Polynomial eigenvalue-counting bound from a pointwise diagonal kernel bound.**

Suppose there are a degree `q : ℕ`, a constant `B ≥ 0`, and a threshold-indexed
family of finite index sets `count : ℝ → Finset (TensorEigenIdx g r s)` such that:

* `hmem` — every index `i` with `1 + λᵢ < Λ` lies in `count Λ`; and
* `hkernel` — the on-diagonal reproducing kernel of `count Λ` is bounded pointwise
  by `B · Λ^q`:
  `∀ Λ x, diagonalKernel g r s (count Λ) x ≤ B · Λ^q`.

Then `EigenvalueCountingBound g r s` holds, with the same family `count`, the same
degree `q`, and constant `A = B · vol(M)` (the total Riemannian volume of the
closed manifold).

The proof integrates the kernel bound over `M`. By
`finsetCard_eq_integral_diagonalKernel`, the cardinality of `count Λ` is the
integral of its diagonal kernel; by monotonicity of the Bochner integral and the
pointwise bound `hkernel`, this is at most the integral of the constant `B · Λ^q`,
which equals `(B · Λ^q) · vol(M) = A · Λ^q`. The total volume is finite because
`M` is compact. This is exactly the integration / volume-normalisation step of the
local-Weyl reproducing-kernel route; the pointwise kernel bound itself is the
geometric input, supplied as the hypothesis `hkernel`. -/
theorem eigenvalueCountingBound_of_pointwiseDiagonalKernelBound
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (q : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (count : ℝ → Finset (TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s))
    (hmem : ∀ (Λ : ℝ) (i : TensorSpectral.TensorEigenIdx (I := I) (M := M) g r s),
      1 + TensorEigenIdx.lambda (I := I) (M := M) i < Λ → i ∈ count Λ)
    (hkernel : ∀ (Λ : ℝ) (x : M),
      diagonalKernel (I := I) (M := M) g r s (count Λ) x ≤ B * Λ ^ q) :
    EigenvalueCountingBound (I := I) (M := M) g r s := by
  haveI hfin : IsFiniteMeasure (riemannianVolumeMeasure (I := I) (M := M) g) :=
    riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (I := I) (M := M) g
  set vol : ℝ :=
    (riemannianVolumeMeasure (I := I) (M := M) g).real Set.univ with hvol_def
  have hvol_nonneg : 0 ≤ vol := by rw [hvol_def]; exact MeasureTheory.measureReal_nonneg
  refine ⟨q, B * vol, mul_nonneg hB hvol_nonneg, count, hmem, ?_⟩
  intro Λ
  rw [finsetCard_eq_integral_diagonalKernel (I := I) (M := M) g r s (count Λ)]
  have h_int_mono :
      ∫ x, diagonalKernel (I := I) (M := M) g r s (count Λ) x
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ∫ _x, B * Λ ^ q ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
    MeasureTheory.integral_mono
      (diagonalKernel_integrable (I := I) (M := M) g r s (count Λ))
      (MeasureTheory.integrable_const _)
      (fun x => hkernel Λ x)
  refine le_trans h_int_mono (le_of_eq ?_)
  rw [MeasureTheory.integral_const, smul_eq_mul, ← hvol_def]
  ring

end MetricRealization
end IntrinsicSpectral
end RicciFlow
end PDE
end DifferentialGeometry

end
