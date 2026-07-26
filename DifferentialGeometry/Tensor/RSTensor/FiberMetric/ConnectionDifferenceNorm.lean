import DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.ConnectionDifference
import DifferentialGeometry.Tensor.RSTensor.TensorRSRiemannian

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Norm Bound for a Connection-Difference Contraction

This file applies the mixed-tensor Hilbert--Schmidt estimate to the contraction
of a connection-difference tensor with a covector.
-/

noncomputable section

namespace Tensor0SBundle

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- Contracting a connection-difference tensor with a covector is bounded by
the mixed Hilbert--Schmidt norm times the covector norm. -/
theorem connOut_norm_le
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g : SmoothMetric_gen I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M} (alpha : Tensor0SSpace 1 I x) :
    Real.sqrt (normSq0S (I := I) g x 2
      (connectionDifferenceOutput (I := I)
        (CovariantDerivative.difference cov cov' x) alpha)) <=
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2
        (connectionDifferenceTensorAt (I := I) cov cov' x)) *
        Real.sqrt (normSq0S (I := I) g x 1 alpha) := by
  change Real.sqrt (normSq0S (I := I) g x 2
      (connectionDifferenceTensorAt (I := I) cov cov' x alpha)) <= _
  exact sqrt_normSqRS_apply (I := I) g
    (connectionDifferenceTensorAt (I := I) cov cov' x) alpha

/-- The tangent-vector `g`-norm of the raw connection difference `(∇ − ∇')` applied to two
tangent vectors is bounded by the mixed Hilbert–Schmidt norm of the connection-difference
tensor times the two vector norms.  This is the vector-output companion of `connOut_norm_le`
(sharp constant `1`): it is the atomic per-slot estimate behind the fibre norm of the
generic-rank connection-difference step `diffStep`, whose evaluation
(`HCGCompactness/MetricCovDerivLinear.diffStep_eval`) inserts exactly
`CovariantDerivative.difference (LC g₁) (LC g₂) x Y X` into one slot of the base tensor.

Route: flatten the output vector `w = (∇−∇') Y X` to the covector `w♭` (so `‖w♭‖ = ‖w‖_g`
and `w♭(w) = ‖w‖²_g`), read `‖w‖²_g` off as the connection-difference `(0,2)` tensor
`connectionDifferenceTensorAt · w♭` evaluated at `(X, Y)`, bound that pointwise evaluation by
its fibre norm (a `g`-orthonormal frame, built internally as in `sqrt_normSqRS_apply`), and
compose with the mixed HS estimate `sqrt_normSqRS_apply` and `‖w♭‖ = ‖w‖_g`; divide by
`‖w‖_g`. -/
theorem connDiffVec_norm_le
    [VectorBundle Real E (TangentSpace I : M -> Type _)]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M -> Type _) I]
    (g : SmoothMetric_gen I M)
    (cov cov' : CovariantDerivative I E (TangentSpace I : M -> Type _))
    {x : M} (X Y : TangentSpace I x) :
    Real.sqrt (g.inner x
        (CovariantDerivative.difference cov cov' x Y X)
        (CovariantDerivative.difference cov cov' x Y X)) <=
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2
        (connectionDifferenceTensorAt (I := I) cov cov' x)) *
        Real.sqrt (g.inner x X X) * Real.sqrt (g.inner x Y Y) := by
  classical
  set w : TangentSpace I x :=
    CovariantDerivative.difference cov cov' x Y X with hw
  set α : Tensor0SSpace 1 I x :=
    dualToCotangent_gen (I := I) (tangentFlatLinear_gen (I := I) g x w) with hα
  -- (1) the flat covector has squared norm `‖w‖²_g`
  have hαnorm : normSq0S (I := I) g x 1 α = g.inner x w w := by
    rw [hα, normSq0S_eq_inner, inner0S_one_eq_cotangent]
    exact cotangentInner_dualToCotangent_tangentFlat_gen (I := I) g x w w
  have hww : 0 <= g.inner x w w := by
    rw [← hαnorm]; exact normSq0S_nonneg (I := I) g x 1 α
  -- (2) `‖w‖²_g` is the connection-difference `(0,2)` tensor evaluated at `(X, Y)`
  have hkey :
      connectionDifferenceTensorAt (I := I) cov cov' x α
          (fun q : Fin 2 => if q = 0 then X else Y) = g.inner x w w := by
    change connectionDifferenceOutput (I := I)
        (CovariantDerivative.difference cov cov' x) α
        (fun q : Fin 2 => if q = 0 then X else Y) = g.inner x w w
    rw [connectionDifferenceOutput_apply_slots, hα, dualToCotangent_apply_gen,
      tangentFlatLinear_apply_gen, ← hw]
  -- (3) internal `g`-orthonormal frame at `x` (as in `sqrt_normSqRS_apply`)
  let D := (tangentMetricData_gen (I := I) g x).metric
  letI : InnerProductSpace.Core Real (TangentSpace I x) := D.toCore
  letI : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup Real (TangentSpace I x) _ _ _ D.toCore
  letI : InnerProductSpace Real (TangentSpace I x) :=
    @InnerProductSpace.ofCore Real (TangentSpace I x) _ _ _ D.toCore.toCore
  let ob := stdOrthonormalBasis Real (TangentSpace I x)
  let basis := ob.toBasis
  have hON : forall i j,
      g.inner x (basis i) (basis j) = if i = j then (1 : Real) else 0 := by
    intro i j
    have hinner : Inner.inner Real (ob i) (ob j) = D.inner (ob i) (ob j) :=
      MetricFiberData.toCore_inner D (ob i) (ob j)
    change g.inner x (ob.toBasis i) (ob.toBasis j) = if i = j then (1 : Real) else 0
    rw [← TangentMetricData_gen.inner_eq_gen
      (tangentMetricData_gen (I := I) g x) (ob.toBasis i) (ob.toBasis j)]
    change D.inner (ob i) (ob j) = if i = j then (1 : Real) else 0
    rw [← hinner]
    exact ob.inner_eq_ite i j
  -- (4) Cauchy–Schwarz apply bound on the `(0,2)` tensor `connectionDifferenceTensorAt · α`
  have hprod :
      (∏ a : Fin 2, Real.sqrt (g.inner x
          ((fun q : Fin 2 => if q = 0 then X else Y) a)
          ((fun q : Fin 2 => if q = 0 then X else Y) a)))
        = Real.sqrt (g.inner x X X) * Real.sqrt (g.inner x Y Y) := by
    rw [Fin.prod_univ_two]; simp
  have habs :
      |connectionDifferenceTensorAt (I := I) cov cov' x α
          (fun q : Fin 2 => if q = 0 then X else Y)| <=
      Real.sqrt (normSq0S (I := I) g x 2
          (connectionDifferenceTensorAt (I := I) cov cov' x α)) *
        (Real.sqrt (g.inner x X X) * Real.sqrt (g.inner x Y Y)) := by
    have h := abs_apply_le_sqrt_normSq0S (I := I) g x 2 basis hON
      (connectionDifferenceTensorAt (I := I) cov cov' x α)
      (fun q : Fin 2 => if q = 0 then X else Y)
    rwa [hprod] at h
  -- (5) mixed HS estimate
  have hHS :
      Real.sqrt (normSq0S (I := I) g x 2
          (connectionDifferenceTensorAt (I := I) cov cov' x α)) <=
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2
          (connectionDifferenceTensorAt (I := I) cov cov' x)) *
        Real.sqrt (normSq0S (I := I) g x 1 α) :=
    sqrt_normSqRS_apply (I := I) g (connectionDifferenceTensorAt (I := I) cov cov' x) α
  -- (6) assemble: `‖w‖²_g ≤ (√normSqRS · √gXX · √gYY) · ‖w‖_g`
  have hchain : g.inner x w w <=
      Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2
          (connectionDifferenceTensorAt (I := I) cov cov' x)) *
        Real.sqrt (g.inner x X X) * Real.sqrt (g.inner x Y Y) *
        Real.sqrt (g.inner x w w) := by
    calc g.inner x w w
          = |connectionDifferenceTensorAt (I := I) cov cov' x α
              (fun q : Fin 2 => if q = 0 then X else Y)| := by
            rw [hkey]; exact (abs_of_nonneg hww).symm
      _ <= Real.sqrt (normSq0S (I := I) g x 2
              (connectionDifferenceTensorAt (I := I) cov cov' x α)) *
            (Real.sqrt (g.inner x X X) * Real.sqrt (g.inner x Y Y)) := habs
      _ <= (Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2
              (connectionDifferenceTensorAt (I := I) cov cov' x)) *
            Real.sqrt (normSq0S (I := I) g x 1 α)) *
            (Real.sqrt (g.inner x X X) * Real.sqrt (g.inner x Y Y)) :=
          mul_le_mul_of_nonneg_right hHS (by positivity)
      _ = Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2
              (connectionDifferenceTensorAt (I := I) cov cov' x)) *
            Real.sqrt (g.inner x X X) * Real.sqrt (g.inner x Y Y) *
            Real.sqrt (g.inner x w w) := by
          rw [hαnorm]; ring
  -- (7) divide by `‖w‖_g`
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (g.inner x w w)) with h0 | hpos
  · rw [← h0]; positivity
  · have hmul : Real.sqrt (g.inner x w w) * Real.sqrt (g.inner x w w) <=
        (Real.sqrt (normSqRS (I := I) (g := g) (x := x) 1 2
            (connectionDifferenceTensorAt (I := I) cov cov' x)) *
          Real.sqrt (g.inner x X X) * Real.sqrt (g.inner x Y Y)) *
          Real.sqrt (g.inner x w w) := by
      rw [Real.mul_self_sqrt hww]; exact hchain
    exact le_of_mul_le_mul_right hmul hpos

end Tensor0SBundle
