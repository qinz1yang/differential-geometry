import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.C4.PullbackField

set_option autoImplicit false

/-!
# Metric-error and tensor-field covariant norms

This file identifies the positive-order covariant norm of a metric tensor field
with the corresponding metric-difference seminorm. Metric compatibility kills
the background metric at every positive covariant order.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff Topology BigOperators
open Tensor0SBundle

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

section PositiveOrder

variable [CompleteSpace E] [I.Boundaryless]
variable [T2Space M] [SigmaCompactSpace M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]

omit [I.Boundaryless] in
/-- At covariant order zero, the metric-tensor error norm is exactly the
metric-difference seminorm. -/
theorem metricError_eq_zero
    (G g : SmoothRiemannianMetric I M) (x : M) :
    metricTensorErrorNorm (I := I)
        (Tensor0SBundle.metricTensorField (I := I) G) g x =
      metricDerivNorm (I := I) 0 G g g x := by
  rfl

/-- At every positive covariant order, the norm of the iterated derivative of
`metricTensorField G` equals the metric-difference seminorm from `G` to the
background metric. -/
theorem t02Norm_metricDiff
    (G g : SmoothRiemannianMetric I M) (a : Nat) (ha : 1 ≤ a) (x : M) :
    tensor02CovDerivNormWith (I := I) a
        (Tensor0SBundle.metricTensorField (I := I) G) g g x =
      metricDerivNorm (I := I) a G g g x := by
  classical
  obtain ⟨basis, hON⟩ :=
    DifferentialGeometry.Integral.Connection.exists_gOrthonormalBasis
      (I := I) g x
  have hinv : Tensor0SBundle.MetricInverseInBasis_gen (I := I) g x basis
      (Tensor0SBundle.identityInvMetric
        (Idx := Fin (Module.finrank Real (TangentSpace I x)))) := by
    have h :=
      DifferentialGeometry.Integral.Connection.metricInverseInBasis_of_orthonormal
        (I := I) g basis hON
    simpa [Tensor0SBundle.identityInvMetric,
      Tensor0SBundle.diagonalInvMetric] using h
  rw [t02Norm_eq_iterCov (I := I)
      (Tensor0SBundle.metricTensorField (I := I) G) g a basis hinv,
    metricDerivNorm_eq_iterCov (I := I) G g g a basis hinv]
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  rw [iterCov_sub, show 1 + b = b + 1 by omega,
    iterCov_metric_zero g b, sub_zero]

end PositiveOrder

section Carrier

variable [CompleteSpace E] [I.Boundaryless]
variable [T2Space M] [SigmaCompactSpace M]
variable [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N]
variable [IsManifold I ∞ N]

/-- Assemble localized pre-approximate-isometry data when a smooth metric
realizes the pullback on the controlled set and all of its metric-difference
seminorms through the requested order are small. -/
noncomputable def PreApproxIsoDataOn.of_metric
    {K : Set M} {eps : Real} {p : Nat} {F : M → N}
    (G g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (heps : 0 < eps) (heps1 : eps < 1)
    (hsmooth : ContMDiffOn I I (∞ : WithTop ℕ∞) F K)
    (happly : ∀ x ∈ K, ∀ v : Fin 2 → TangentSpace I x,
      Tensor0SBundle.metricTensorField (I := I) G x v =
        h.inner (F x)
          (mfderiv I I F x (v 0)) (mfderiv I I F x (v 1)))
    (hderiv : ∀ a : Nat, a ≤ p → ∀ x ∈ K,
      metricDerivNorm (I := I) a G g g x ≤ eps) :
    PreApproxIsoDataOn (I := I) K eps p F g h where
  eps_pos := heps
  eps_lt_one := heps1
  smoothOn := hsmooth
  pullback := Tensor0SBundle.metricTensorField (I := I) G
  pullback_apply := happly
  c0_small := by
    intro x hx
    rw [metricError_eq_zero (I := I) G g x]
    exact hderiv 0 (Nat.zero_le p) x hx
  cov_deriv_small := by
    intro a ha hap x hx
    rw [t02Norm_metricDiff (I := I) G g a ha x]
    exact hderiv a hap x hx

end Carrier

/-- A uniform component bound in an orthonormal basis for `g0`, followed by a
pointwise metric-equivalence bound from `g0` to `g`, controls the intrinsic
`g`-norm of a covariant tensor. -/
theorem sqrt_norm_le_comp
    {Idx : Type*} [Fintype Idx] [DecidableEq Idx]
    (g0 g : SmoothMetric_gen I M) (x : M) (s : Nat)
    (basis : Module.Basis Idx Real (TangentSpace I x))
    (hinv0 : MetricInverseInBasis_gen (I := I) g0 x basis
      (identityInvMetric (Idx := Idx)))
    {C B : Real} (hC : 1 ≤ C)
    (hequiv : ∀ v : TangentSpace I x,
      C⁻¹ * g0.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ C * g0.inner x v v)
    (T : Tensor0SSpace s I x) (hBnn : 0 ≤ B)
    (hB : ∀ slots : Fin s → Idx,
      |component0S (I := I) basis T slots| ≤ B) :
    Real.sqrt (normSq0S (I := I) g x s T) ≤
      Real.sqrt (C ^ s) *
        (Real.sqrt (Fintype.card (Fin s → Idx) : Real) * B) := by
  have hflat := normSq0S_le_card_of_component_bound
    (I := I) g0 x s basis hinv0 T B hBnn hB
  have hroot : Real.sqrt (normSq0S (I := I) g0 x s T) ≤
      Real.sqrt (Fintype.card (Fin s → Idx) : Real) * B := by
    calc
      Real.sqrt (normSq0S (I := I) g0 x s T) ≤
          Real.sqrt ((Fintype.card (Fin s → Idx) : Real) * B ^ 2) :=
        Real.sqrt_le_sqrt hflat
      _ = Real.sqrt (Fintype.card (Fin s → Idx) : Real) *
          Real.sqrt (B ^ 2) :=
        Real.sqrt_mul (by positivity) _
      _ = Real.sqrt (Fintype.card (Fin s → Idx) : Real) * B := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hBnn]
  exact (sqrt_normSq0S_le_of_metric_equiv (I := I)
    g0 g x s hC hequiv T).trans
      (mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _))

end HCGCompactness
end DifferentialGeometry
