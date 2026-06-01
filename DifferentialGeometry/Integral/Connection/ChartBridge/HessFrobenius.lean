import DifferentialGeometry.Integral.Connection.ChartBridge.Hessian

/-!
# Bridge between the chart Hessian Frobenius square and the abstract-Hessian Frobenius
square

This file packages the identity between the chart-coordinate metric Frobenius norm
squared `chartHessFrobeniusSq g f x = ∑_{ijkl} G^{ik}(x, x) G^{jl}(x, x) H_{ij}(x, x)
H_{kl}(x, x)` (where `H = chartHessianTensor g x f` and `G^{ij} = chartInvGramMatrix
g x x`) and the basis-naive Frobenius square `frobeniusSqFun (abstractHessianBilin g
f) x = ∑_{ij} (abstractHessian g f x e_i e_j)²` of the abstract Hessian carrier.

The chart-Frobenius `chartHessFrobeniusSq` is a basis-independent geometric quantity:
it uses the inverse Gram matrix `G^{ij}(x, x)` to raise both index pairs of the Hessian
matrix `H_{ij}` and contract. The basis-naive `frobeniusSqFun` instead computes the sum
of squares of the matrix entries against the canonical model basis `Module.finBasis ℝ E`,
without using the metric.

The two quantities coincide pointwise at `x` precisely when the canonical chart at `x`,
evaluated at `x` itself, is `g`-orthonormal — equivalently, when `chartInvGramMatrix g x
x i j = δ^{ij}`. Under this orthonormality assumption, the chain `chartHessFrobeniusSq
g f x = frobeniusSqFun (hessFun g f) x = frobeniusSqFun (abstractHessianBilin g f) x`
links the chart Hessian to the abstract Hessian through the unconditional matrix identity
`chartHessianMatrixIdentity_holds`.

## Main theorems

* `chartHessFrobeniusSq_eq_frobeniusSqFun_hessFun_of_orthonormal` — the chart Hessian
  metric Frobenius square equals the basis-naive Frobenius square of `hessFun g f`,
  under the orthonormality hypothesis.
* `chartHessFrobeniusSq_eq_metric_hessian_norm_sq` — the chart Hessian metric Frobenius
  square equals the basis-naive Frobenius square of the abstract Hessian carrier
  `abstractHessianBilin g f`, under the same orthonormality hypothesis.

## Strategy

Since the BochnerIdentity development that originally exposed
`chartHessFrobeniusSq_eq_frobeniusSqFun_of_orthonormal` is presently unavailable, the
orthonormality form of the chart-Frobenius / basis-Frobenius identification is reproved
locally in this file. The proof unfolds both sides into their explicit chart-coordinate
sums, reduces the inverse Gram matrix to Kronecker deltas via the orthonormality
hypothesis, and collapses the two redundant indices in the standard way.

The bridge to the abstract Hessian carrier then follows from the unconditional matrix
identity `chartHessianMatrixIdentity_holds`, packaged on the Frobenius norm by
`frobeniusSqFun_hessFun_eq_frobeniusSqFun_abstractHessianBilin_of_matrix_identity`.
-/

noncomputable section

open Bundle Manifold Set FiberBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace Integral
namespace Connection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

/-- **Chart Frobenius equals basis-naive Frobenius of `hessFun` under orthonormality.**
Conditional on the chart at `x` being `g`-orthonormal at `x` (i.e. the inverse Gram
matrix at `x` is the identity), the chart Hessian metric Frobenius square equals the
basis-naive Frobenius square of `hessFun g f` at `x`. -/
theorem chartHessFrobeniusSq_eq_frobeniusSqFun_hessFun_of_orthonormal
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    chartHessFrobeniusSq (I := I) g f x =
      frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x := by
  classical
  rw [chartHessFrobeniusSq_def, frobeniusSqFun_hessFun]
  have hLHS_eq :
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramMatrix (I := I) g x x i k *
            chartInvGramMatrix (I := I) g x x j l *
              chartHessianTensor (I := I) g x f i j x *
                chartHessianTensor (I := I) g x f k l x) =
      (∑ i : Fin (Module.finrank ℝ E),
        ∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (if i = k then (1 : ℝ) else 0) *
            (if j = l then (1 : ℝ) else 0) *
              chartHessianTensor (I := I) g x f i j x *
                chartHessianTensor (I := I) g x f k l x) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [h_orth i k, h_orth j l]
  rw [hLHS_eq]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hl : ∀ k : Fin (Module.finrank ℝ E),
      ∑ l : Fin (Module.finrank ℝ E),
        (if i = k then (1 : ℝ) else 0) *
          (if j = l then (1 : ℝ) else 0) *
            chartHessianTensor (I := I) g x f i j x *
              chartHessianTensor (I := I) g x f k l x =
        (if i = k then (1 : ℝ) else 0) *
          chartHessianTensor (I := I) g x f i j x *
          chartHessianTensor (I := I) g x f k j x := by
    intro k
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
      ring
    · intro l _ hlj
      have hjl : ¬ j = l := fun h => hlj h.symm
      rw [if_neg hjl]
      ring
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [show
      (∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          (if i = k then (1 : ℝ) else 0) *
            (if j = l then (1 : ℝ) else 0) *
              chartHessianTensor (I := I) g x f i j x *
                chartHessianTensor (I := I) g x f k l x) =
      ∑ k : Fin (Module.finrank ℝ E),
        (if i = k then (1 : ℝ) else 0) *
          chartHessianTensor (I := I) g x f i j x *
          chartHessianTensor (I := I) g x f k j x from
    Finset.sum_congr rfl (fun k _ => hl k)]
  rw [Finset.sum_eq_single i]
  · rw [if_pos rfl]
    ring
  · intro k _ hki
    have hik : ¬ i = k := fun h => hki h.symm
    rw [if_neg hik]
    ring
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **Chart Hessian Frobenius square equals abstract Hessian Frobenius square — under
orthonormality.** Conditional on the chart at `x` being `g`-orthonormal at `x`, the
chart Hessian metric Frobenius square equals the basis-naive Frobenius square of the
abstract Hessian carrier `abstractHessianBilin g f` at `x`.

The proof chains: (1) Step 1 above bridges the chart Frobenius to the basis-naive
Frobenius of `hessFun g f`; (2) the unconditional matrix identity (packaged on the
Frobenius norm by `frobeniusSqFun_hessFun_eq_frobeniusSqFun_abstractHessianBilin_of_matrix_identity`)
bridges to `abstractHessianBilin g f`. -/
theorem chartHessFrobeniusSq_eq_metric_hessian_norm_sq [I.Boundaryless]
    (g : SmoothRiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (x : M)
    (h_orth : ∀ i j : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := I) g x x i j = if i = j then (1 : ℝ) else 0) :
    chartHessFrobeniusSq (I := I) g f x =
      frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x := by
  classical
  have h1 : chartHessFrobeniusSq (I := I) g f x =
      frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x :=
    chartHessFrobeniusSq_eq_frobeniusSqFun_hessFun_of_orthonormal
      (I := I) g f x h_orth
  have hM : chartHessianMatrixIdentity (I := I) g f x :=
    chartHessianMatrixIdentity_holds (I := I) g hf x
  have h2 : frobeniusSqFun (I := I) (M := M) (hessFun (I := I) g f) x =
      frobeniusSqFun (I := I) (M := M) (abstractHessianBilin (I := I) g f) x :=
    frobeniusSqFun_hessFun_eq_frobeniusSqFun_abstractHessianBilin_of_matrix_identity
      (I := I) g f x hM
  exact h1.trans h2

end Connection
end Integral
end DifferentialGeometry
